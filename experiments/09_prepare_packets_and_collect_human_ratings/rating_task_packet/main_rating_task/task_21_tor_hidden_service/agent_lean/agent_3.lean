import Mathlib

/-!
# 129_unsafeTorHiddenService

Lean 4 formalization of the Python program `unsafe_tor_rendezvous`.

The Python function models an **unsafe** Tor hidden-service rendezvous
protocol: the hidden service never authenticates or vets the rendezvous
point, so the function returns `True` for every input, regardless of whether
the rendezvous point is controlled by an adversary.

Vulnerability (MIT 6.858 Fall 2012 Quiz 2): a malicious Tor onion router can
set up a rendezvous point on itself and send its address to the introduction
point of a hidden service.  When the hidden service connects, the malicious
node records the origin of the incoming connection, deanonymizing the service.

Inputs (mirroring the Python signature):

* `rendezvousAddr : Int`        -- the (IPv4-style) address of the rendezvous point,
* `isMalicious : Bool`          -- whether the rendezvous point is adversary-controlled,
* `hiddenServiceConnects : Bool` -- whether the hidden service actually connects to it.

The file contains the functional implementation, unit tests mirroring the
Python `check()` function, a pre-condition, properties with proofs, a
post-condition, property-based tests, the correctness theorem, an imperative
implementation using `Id.run do`, and the functional/imperative equivalence
theorem.
-/

namespace «129_unsafeTorHiddenService»

/-! ## Functional implementation -/

set_option linter.unusedVariables false in
/-- Functional implementation of `unsafe_tor_rendezvous`.

Returns `true` regardless of whether the rendezvous point is controlled by an
adversary: the rendezvous point is never authenticated or vetted. -/
def unsafeTorRendezvous (rendezvousAddr : Int) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) : Bool :=
  true  -- vulnerable: rendezvous never authenticated

/-- Lean counterpart of the Python `check()` function: the conjunction of its
four assertions. -/
def check : Bool :=
  (unsafeTorRendezvous 0x0A000001 false true == true) &&   -- honest rendezvous accepted
  (unsafeTorRendezvous 0xDEADBEEF true true == true) &&    -- vuln: malicious rendezvous accepted
  (unsafeTorRendezvous 0x00000000 true false == true) &&   -- vuln: no-connect malicious accepted
  (unsafeTorRendezvous 0x7F000001 false false == true)     -- localhost honest accepted

/-! ## Unit tests (mirroring the Python `check()` assertions) -/

example : unsafeTorRendezvous 0x0A000001 false true = true := by native_decide
example : unsafeTorRendezvous 0xDEADBEEF true true = true := by native_decide
example : unsafeTorRendezvous 0x00000000 true false = true := by native_decide
example : unsafeTorRendezvous 0x7F000001 false false = true := by native_decide
example : check = true := by native_decide

#eval unsafeTorRendezvous 0x0A000001 false true   -- true
#eval unsafeTorRendezvous 0xDEADBEEF true true    -- true
#eval unsafeTorRendezvous 0x00000000 true false   -- true
#eval unsafeTorRendezvous 0x7F000001 false false  -- true
#eval check                                       -- true

/-- The Python `check()` function succeeds (all four assertions hold). -/
theorem check_thm : check = true := by
  decide

/-! ## Pre-condition -/

set_option linter.unusedVariables false in
/-- Pre-condition: the Python function accepts any `int` address together with
any two Booleans.  There is no restriction on the inputs. -/
def Pre (rendezvousAddr : Int) (isMalicious : Bool) (hiddenServiceConnects : Bool) : Prop :=
  True

/-! ## Properties -/

/-- Property: the rendezvous point is always accepted, whatever the inputs. -/
def always_accepts_prop (rendezvousAddr : Int) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) : Prop :=
  unsafeTorRendezvous rendezvousAddr isMalicious hiddenServiceConnects = true

theorem always_accepts_thm (rendezvousAddr : Int) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) :
    always_accepts_prop rendezvousAddr isMalicious hiddenServiceConnects := by
  unfold always_accepts_prop unsafeTorRendezvous
  rfl

/-- Property (the vulnerability): a rendezvous point controlled by an adversary
is accepted, whether or not the hidden service then connects to it. -/
def malicious_accepted_prop (rendezvousAddr : Int) (hiddenServiceConnects : Bool) : Prop :=
  unsafeTorRendezvous rendezvousAddr true hiddenServiceConnects = true

theorem malicious_accepted_thm (rendezvousAddr : Int) (hiddenServiceConnects : Bool) :
    malicious_accepted_prop rendezvousAddr hiddenServiceConnects := by
  unfold malicious_accepted_prop unsafeTorRendezvous
  rfl

/-- Property: an honest rendezvous point is accepted (the honest path works;
otherwise the Python assertions "honest rendezvous rejected" would fire). -/
def honest_accepted_prop (rendezvousAddr : Int) (hiddenServiceConnects : Bool) : Prop :=
  unsafeTorRendezvous rendezvousAddr false hiddenServiceConnects = true

theorem honest_accepted_thm (rendezvousAddr : Int) (hiddenServiceConnects : Bool) :
    honest_accepted_prop rendezvousAddr hiddenServiceConnects := by
  unfold honest_accepted_prop unsafeTorRendezvous
  rfl

/-- Property: the verdict does not depend on whether the rendezvous point is
malicious, i.e. no authentication of the rendezvous point takes place. -/
def no_authentication_prop (rendezvousAddr : Int) (hiddenServiceConnects : Bool) : Prop :=
  unsafeTorRendezvous rendezvousAddr true hiddenServiceConnects =
    unsafeTorRendezvous rendezvousAddr false hiddenServiceConnects

theorem no_authentication_thm (rendezvousAddr : Int) (hiddenServiceConnects : Bool) :
    no_authentication_prop rendezvousAddr hiddenServiceConnects := by
  unfold no_authentication_prop unsafeTorRendezvous
  rfl

/-- Property: the verdict does not depend on the rendezvous address, i.e. the
address received from the introduction point is never vetted. -/
def address_ignored_prop (addr₁ addr₂ : Int) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) : Prop :=
  unsafeTorRendezvous addr₁ isMalicious hiddenServiceConnects =
    unsafeTorRendezvous addr₂ isMalicious hiddenServiceConnects

theorem address_ignored_thm (addr₁ addr₂ : Int) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) :
    address_ignored_prop addr₁ addr₂ isMalicious hiddenServiceConnects := by
  unfold address_ignored_prop unsafeTorRendezvous
  rfl

/-- Property: the verdict does not depend on whether the hidden service
connects to the rendezvous point. -/
def connect_ignored_prop (rendezvousAddr : Int) (isMalicious : Bool) : Prop :=
  unsafeTorRendezvous rendezvousAddr isMalicious true =
    unsafeTorRendezvous rendezvousAddr isMalicious false

theorem connect_ignored_thm (rendezvousAddr : Int) (isMalicious : Bool) :
    connect_ignored_prop rendezvousAddr isMalicious := by
  unfold connect_ignored_prop unsafeTorRendezvous
  rfl

/-- Deanonymization scenario from the docstring: the hidden service is
deanonymized exactly when the rendezvous point is malicious, the hidden
service connects to it, and the protocol accepted the rendezvous point (so the
malicious node can record the origin of the incoming connection). -/
def deanonymized (rendezvousAddr : Int) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) : Bool :=
  isMalicious && hiddenServiceConnects &&
    unsafeTorRendezvous rendezvousAddr isMalicious hiddenServiceConnects

/-- Property (the attack succeeds): for every address, a malicious rendezvous
point that the hidden service connects to deanonymizes the service. -/
def deanonymization_prop (rendezvousAddr : Int) : Prop :=
  deanonymized rendezvousAddr true true = true

theorem deanonymization_thm (rendezvousAddr : Int) :
    deanonymization_prop rendezvousAddr := by
  unfold deanonymization_prop deanonymized unsafeTorRendezvous
  rfl

/-! ## Post-condition -/

/-- Post-condition: conjunction of all properties above. -/
def Post_prop (rendezvousAddr : Int) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) : Prop :=
  always_accepts_prop rendezvousAddr isMalicious hiddenServiceConnects ∧
  malicious_accepted_prop rendezvousAddr hiddenServiceConnects ∧
  honest_accepted_prop rendezvousAddr hiddenServiceConnects ∧
  no_authentication_prop rendezvousAddr hiddenServiceConnects ∧
  (∀ addr₂ : Int, address_ignored_prop rendezvousAddr addr₂ isMalicious hiddenServiceConnects) ∧
  connect_ignored_prop rendezvousAddr isMalicious ∧
  deanonymization_prop rendezvousAddr

/-! ## Property-based tests -/

-- always_accepts_prop
#eval Plausible.Testable.check
  (∀ (addr : Int) (isMalicious hiddenServiceConnects : Bool),
    unsafeTorRendezvous addr isMalicious hiddenServiceConnects = true)

-- malicious_accepted_prop
#eval Plausible.Testable.check
  (∀ (addr : Int) (hiddenServiceConnects : Bool),
    unsafeTorRendezvous addr true hiddenServiceConnects = true)

-- honest_accepted_prop
#eval Plausible.Testable.check
  (∀ (addr : Int) (hiddenServiceConnects : Bool),
    unsafeTorRendezvous addr false hiddenServiceConnects = true)

-- no_authentication_prop
#eval Plausible.Testable.check
  (∀ (addr : Int) (hiddenServiceConnects : Bool),
    unsafeTorRendezvous addr true hiddenServiceConnects =
      unsafeTorRendezvous addr false hiddenServiceConnects)

-- address_ignored_prop
#eval Plausible.Testable.check
  (∀ (addr₁ addr₂ : Int) (isMalicious hiddenServiceConnects : Bool),
    unsafeTorRendezvous addr₁ isMalicious hiddenServiceConnects =
      unsafeTorRendezvous addr₂ isMalicious hiddenServiceConnects)

-- connect_ignored_prop
#eval Plausible.Testable.check
  (∀ (addr : Int) (isMalicious : Bool),
    unsafeTorRendezvous addr isMalicious true = unsafeTorRendezvous addr isMalicious false)

-- deanonymization_prop
#eval Plausible.Testable.check
  (∀ (addr : Int), deanonymized addr true true = true)

/-- Executable Boolean form of `Post_prop`.  The universally quantified second
address of the address-independence conjunct is supplied as the extra argument
`addr₂`, so that it can be sampled by the property-based tests. -/
def postCheck (rendezvousAddr addr₂ : Int) (isMalicious hiddenServiceConnects : Bool) : Bool :=
  (unsafeTorRendezvous rendezvousAddr isMalicious hiddenServiceConnects == true) &&
  (unsafeTorRendezvous rendezvousAddr true hiddenServiceConnects == true) &&
  (unsafeTorRendezvous rendezvousAddr false hiddenServiceConnects == true) &&
  (unsafeTorRendezvous rendezvousAddr true hiddenServiceConnects ==
    unsafeTorRendezvous rendezvousAddr false hiddenServiceConnects) &&
  (unsafeTorRendezvous rendezvousAddr isMalicious hiddenServiceConnects ==
    unsafeTorRendezvous addr₂ isMalicious hiddenServiceConnects) &&
  (unsafeTorRendezvous rendezvousAddr isMalicious true ==
    unsafeTorRendezvous rendezvousAddr isMalicious false) &&
  (deanonymized rendezvousAddr true true == true)

-- Post_prop (randomized)
#eval Plausible.Testable.check
  (∀ (addr₁ addr₂ : Int) (isMalicious hiddenServiceConnects : Bool),
    postCheck addr₁ addr₂ isMalicious hiddenServiceConnects = true)

/-- Sample addresses for the bounded tests: the Python test addresses, their
neighbours, a negative value and small values. -/
def sampleAddrs : List Int :=
  [0x0A000001, 0xDEADBEEF, 0x00000000, 0x7F000001, 0xFFFFFFFF, 0x100000000, -1, -0xDEADBEEF] ++
    (List.range 32).map (fun n => (n : Int))

-- Post_prop (bounded, exhaustive over `sampleAddrs` × `sampleAddrs` × Bool × Bool)
example :
    (sampleAddrs.all fun addr₁ => sampleAddrs.all fun addr₂ =>
      [true, false].all fun isMalicious => [true, false].all fun hiddenServiceConnects =>
        postCheck addr₁ addr₂ isMalicious hiddenServiceConnects) = true := by
  native_decide

-- always_accepts_prop (bounded)
example :
    (sampleAddrs.all fun addr => [true, false].all fun isMalicious =>
      [true, false].all fun hiddenServiceConnects =>
        unsafeTorRendezvous addr isMalicious hiddenServiceConnects) = true := by
  native_decide

/-! ## Correctness theorem -/

/-- Correctness: the pre-condition implies the post-condition. -/
theorem correctness_thm (rendezvousAddr : Int) (isMalicious : Bool)
    (hiddenServiceConnects : Bool)
    (_hpre : Pre rendezvousAddr isMalicious hiddenServiceConnects) :
    Post_prop rendezvousAddr isMalicious hiddenServiceConnects := by
  unfold Post_prop
  exact ⟨always_accepts_thm rendezvousAddr isMalicious hiddenServiceConnects,
    malicious_accepted_thm rendezvousAddr hiddenServiceConnects,
    honest_accepted_thm rendezvousAddr hiddenServiceConnects,
    no_authentication_thm rendezvousAddr hiddenServiceConnects,
    fun addr₂ => address_ignored_thm rendezvousAddr addr₂ isMalicious hiddenServiceConnects,
    connect_ignored_thm rendezvousAddr isMalicious,
    deanonymization_thm rendezvousAddr⟩

/-! ## Imperative implementation -/

set_option linter.unusedVariables false in
/-- Imperative implementation of `unsafe_tor_rendezvous` using `Id.run do`
with mutable state.  The hidden service receives the rendezvous address from
the introduction point and, without authenticating or vetting the rendezvous
point, accepts it. -/
def unsafeTorRendezvousImp (rendezvousAddr : Int) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) : Bool := Id.run do
  -- Verdict of the hidden service on the proposed rendezvous point.
  let mut accepted : Bool := false
  -- A safe protocol would authenticate the rendezvous point here, using
  -- `rendezvousAddr` and rejecting when `isMalicious`.  The vulnerable code
  -- performs no such check: the rendezvous point is accepted unconditionally.
  accepted := true
  -- Whether the hidden service then connects (`hiddenServiceConnects`) does not
  -- change the verdict either.
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

-- functional = imperative (randomized)
#eval Plausible.Testable.check
  (∀ (addr : Int) (isMalicious hiddenServiceConnects : Bool),
    unsafeTorRendezvous addr isMalicious hiddenServiceConnects =
      unsafeTorRendezvousImp addr isMalicious hiddenServiceConnects)

-- functional = imperative (bounded)
example :
    (sampleAddrs.all fun addr => [true, false].all fun isMalicious =>
      [true, false].all fun hiddenServiceConnects =>
        unsafeTorRendezvous addr isMalicious hiddenServiceConnects ==
          unsafeTorRendezvousImp addr isMalicious hiddenServiceConnects) = true := by
  native_decide

/-! ## Equivalence theorem -/

/-- The functional and imperative implementations agree on every input. -/
theorem functional_imperative_equiv_thm (rendezvousAddr : Int) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) :
    unsafeTorRendezvous rendezvousAddr isMalicious hiddenServiceConnects =
      unsafeTorRendezvousImp rendezvousAddr isMalicious hiddenServiceConnects := by
  unfold unsafeTorRendezvous unsafeTorRendezvousImp
  rfl

end «129_unsafeTorHiddenService»
