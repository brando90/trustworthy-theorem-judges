import Mathlib

/-!
# Unsafe Tor hidden-service rendezvous

This file translates Python's `unsafe_tor_rendezvous`. The function always returns
`true`: it neither authenticates the rendezvous point nor checks that the hidden
service connects. In particular, a malicious rendezvous point is accepted.

Python's arbitrary-precision integer address is represented by `Int`, without
restricting it to an IP address range. The network interaction and recording of
an origin described in the Python comments are outside this function's behavior.
The proofs and tests characterize its unconditional acceptance and its
independence from every input.
-/

namespace UnsafeTorHiddenService

/-! ## Functional implementation -/

def unsafe_tor_rendezvous (_rendezvous_addr : Int) (_is_malicious : Bool)
    (_hidden_service_connects : Bool) : Bool :=
  true

/-! ## Unit tests from Python's `check` -/

example : unsafe_tor_rendezvous 0x0A000001 false true = true := by native_decide
example : unsafe_tor_rendezvous 0xDEADBEEF true true = true := by native_decide
example : unsafe_tor_rendezvous 0x00000000 true false = true := by native_decide
example : unsafe_tor_rendezvous 0x7F000001 false false = true := by native_decide

#eval unsafe_tor_rendezvous 0x0A000001 false true
#eval unsafe_tor_rendezvous 0xDEADBEEF true true
#eval unsafe_tor_rendezvous 0x00000000 true false
#eval unsafe_tor_rendezvous 0x7F000001 false false

/-! ## Preconditions and semantic properties -/

/-- All integer addresses and all combinations of flags are admissible. -/
def Pre (_rendezvous_addr : Int) (_is_malicious _hidden_service_connects : Bool) : Prop :=
  True

def always_accepts_prop (rendezvous_addr : Int)
    (is_malicious hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects = true

theorem always_accepts_thm (rendezvous_addr : Int)
    (is_malicious hidden_service_connects : Bool) :
    always_accepts_prop rendezvous_addr is_malicious hidden_service_connects := by
  rfl

/-- The vulnerability remains present whether or not the hidden service connects. -/
def malicious_accepted_prop (rendezvous_addr : Int)
    (hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr true hidden_service_connects = true

theorem malicious_accepted_thm (rendezvous_addr : Int) (hidden_service_connects : Bool) :
    malicious_accepted_prop rendezvous_addr hidden_service_connects := by
  rfl

def address_independent_prop (rendezvous_addr : Int)
    (is_malicious hidden_service_connects : Bool) : Prop :=
  ∀ other_addr : Int,
    unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects =
      unsafe_tor_rendezvous other_addr is_malicious hidden_service_connects

theorem address_independent_thm (rendezvous_addr : Int)
    (is_malicious hidden_service_connects : Bool) :
    address_independent_prop rendezvous_addr is_malicious hidden_service_connects := by
  intro other_addr
  rfl

def maliciousness_independent_prop (rendezvous_addr : Int)
    (is_malicious hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects =
    unsafe_tor_rendezvous rendezvous_addr (!is_malicious) hidden_service_connects

theorem maliciousness_independent_thm (rendezvous_addr : Int)
    (is_malicious hidden_service_connects : Bool) :
    maliciousness_independent_prop rendezvous_addr is_malicious hidden_service_connects := by
  rfl

def connection_independent_prop (rendezvous_addr : Int)
    (is_malicious hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects =
    unsafe_tor_rendezvous rendezvous_addr is_malicious (!hidden_service_connects)

theorem connection_independent_thm (rendezvous_addr : Int)
    (is_malicious hidden_service_connects : Bool) :
    connection_independent_prop rendezvous_addr is_malicious hidden_service_connects := by
  rfl

/-- The complete postcondition is the conjunction of the properties above. -/
def Post_prop (rendezvous_addr : Int)
    (is_malicious hidden_service_connects : Bool) : Prop :=
  always_accepts_prop rendezvous_addr is_malicious hidden_service_connects ∧
  malicious_accepted_prop rendezvous_addr hidden_service_connects ∧
  address_independent_prop rendezvous_addr is_malicious hidden_service_connects ∧
  maliciousness_independent_prop rendezvous_addr is_malicious hidden_service_connects ∧
  connection_independent_prop rendezvous_addr is_malicious hidden_service_connects

/-! ## Property-based tests

Each test checks an executable form of its named property on generated inputs.
For address independence and the postcondition, the universally quantified
comparison address is sampled alongside the original inputs. These tests are
evidence in addition to the proofs, and are never used to discharge a theorem.
-/

-- PBT: always_accepts_prop.
#eval Plausible.Testable.check (∀ (addr : Int) (malicious connects : Bool),
  unsafe_tor_rendezvous addr malicious connects = true)

-- PBT: malicious_accepted_prop.
#eval Plausible.Testable.check (∀ (addr : Int) (connects : Bool),
  unsafe_tor_rendezvous addr true connects = true)

-- PBT: address_independent_prop.
#eval Plausible.Testable.check (∀ (addr other_addr : Int) (malicious connects : Bool),
  unsafe_tor_rendezvous addr malicious connects =
    unsafe_tor_rendezvous other_addr malicious connects)

-- PBT: maliciousness_independent_prop.
#eval Plausible.Testable.check (∀ (addr : Int) (malicious connects : Bool),
  unsafe_tor_rendezvous addr malicious connects =
    unsafe_tor_rendezvous addr (!malicious) connects)

-- PBT: connection_independent_prop.
#eval Plausible.Testable.check (∀ (addr : Int) (malicious connects : Bool),
  unsafe_tor_rendezvous addr malicious connects =
    unsafe_tor_rendezvous addr malicious (!connects))

-- PBT: Post_prop, checking all five conjuncts together as Booleans.
#eval Plausible.Testable.check (∀ (addr other_addr : Int) (malicious connects : Bool),
  ((unsafe_tor_rendezvous addr malicious connects == true) &&
    (unsafe_tor_rendezvous addr true connects == true) &&
    (unsafe_tor_rendezvous addr malicious connects ==
      unsafe_tor_rendezvous other_addr malicious connects) &&
    (unsafe_tor_rendezvous addr malicious connects ==
      unsafe_tor_rendezvous addr (!malicious) connects) &&
    (unsafe_tor_rendezvous addr malicious connects ==
      unsafe_tor_rendezvous addr malicious (!connects))) = true)

/-- Signed small addresses, the Python examples, and integers beyond 64-bit bounds. -/
def testAddresses : List Int :=
  (List.range 33).map (fun n => (n : Int) - 16) ++
    [0x0A000001, 0xDEADBEEF, 0x00000000, 0x7F000001, -(2 ^ 80), 2 ^ 80]

-- Bounded PBT: all five Post_prop conjuncts, every address pair, and all four flag pairs.
example :
    testAddresses.all (fun addr =>
      testAddresses.all (fun other_addr =>
        [false, true].all (fun malicious =>
          [false, true].all (fun connects =>
            (unsafe_tor_rendezvous addr malicious connects == true) &&
            (unsafe_tor_rendezvous addr true connects == true) &&
            (unsafe_tor_rendezvous addr malicious connects ==
              unsafe_tor_rendezvous other_addr malicious connects) &&
            (unsafe_tor_rendezvous addr malicious connects ==
              unsafe_tor_rendezvous addr (!malicious) connects) &&
            (unsafe_tor_rendezvous addr malicious connects ==
              unsafe_tor_rendezvous addr malicious (!connects)))))) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (rendezvous_addr : Int)
    (is_malicious hidden_service_connects : Bool) :
    Pre rendezvous_addr is_malicious hidden_service_connects →
      Post_prop rendezvous_addr is_malicious hidden_service_connects := by
  intro _hPre
  exact ⟨always_accepts_thm rendezvous_addr is_malicious hidden_service_connects,
    malicious_accepted_thm rendezvous_addr hidden_service_connects,
    address_independent_thm rendezvous_addr is_malicious hidden_service_connects,
    maliciousness_independent_thm rendezvous_addr is_malicious hidden_service_connects,
    connection_independent_thm rendezvous_addr is_malicious hidden_service_connects⟩

/-! ## Imperative implementation and tests -/

def unsafe_tor_rendezvous_imperative (_rendezvous_addr : Int) (_is_malicious : Bool)
    (_hidden_service_connects : Bool) : Bool := Id.run do
  let mut accepted := false
  accepted := true
  return accepted

example : unsafe_tor_rendezvous_imperative 0x0A000001 false true = true := by native_decide
example : unsafe_tor_rendezvous_imperative 0xDEADBEEF true true = true := by native_decide
example : unsafe_tor_rendezvous_imperative 0x00000000 true false = true := by native_decide
example : unsafe_tor_rendezvous_imperative 0x7F000001 false false = true := by native_decide

#eval unsafe_tor_rendezvous_imperative 0x0A000001 false true
#eval unsafe_tor_rendezvous_imperative 0xDEADBEEF true true
#eval unsafe_tor_rendezvous_imperative 0x00000000 true false
#eval unsafe_tor_rendezvous_imperative 0x7F000001 false false

-- PBT: functional-imperative equivalence on generated inputs.
#eval Plausible.Testable.check (∀ (addr : Int) (malicious connects : Bool),
  unsafe_tor_rendezvous addr malicious connects =
    unsafe_tor_rendezvous_imperative addr malicious connects)

theorem functional_imperative_equivalence_thm (rendezvous_addr : Int)
    (is_malicious hidden_service_connects : Bool) :
    unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects =
      unsafe_tor_rendezvous_imperative rendezvous_addr is_malicious hidden_service_connects := by
  rfl

end UnsafeTorHiddenService
