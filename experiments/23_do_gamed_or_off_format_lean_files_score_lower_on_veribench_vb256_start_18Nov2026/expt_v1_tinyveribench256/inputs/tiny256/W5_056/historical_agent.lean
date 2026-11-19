import Mathlib
namespace Agent

/-!
# Unsafe Tor hidden-service rendezvous

Translation of the Python `unsafe_tor_rendezvous` and its four checks.
The function unconditionally accepts a rendezvous: it neither authenticates the
rendezvous address nor inspects the maliciousness or connection flags. `Int`
models Python's unbounded integers, including negative addresses; there is no
address-validity precondition.

This deliberately preserves the vulnerable behavior described in MIT 6.858
Fall 2012 Quiz 2, rather than repairing it. The Boolean result models acceptance
only. Actual networking, origin recording, and deanonymization are not operations
performed by the source function and are not asserted to occur by this model.
-/

namespace UnsafeTorHiddenService

/-! ## Functional implementation -/

/-- Like the Python function, return `true` without inspecting any argument. -/
def unsafe_tor_rendezvous
    (_rendezvous_addr : Int) (_is_malicious _hidden_service_connects : Bool) : Bool :=
  true

/-! ## Unit tests and the Python check routine -/

example : unsafe_tor_rendezvous 0x0A000001 false true = true := by native_decide
example : unsafe_tor_rendezvous 0xDEADBEEF true true = true := by native_decide
example : unsafe_tor_rendezvous 0x00000000 true false = true := by native_decide
example : unsafe_tor_rendezvous 0x7F000001 false false = true := by native_decide

/-- Run the same assertions, diagnostic messages, and success message as Python. -/
def check : IO Unit := do
  unless unsafe_tor_rendezvous 0x0A000001 false true do
    throw (IO.userError "honest rendezvous rejected")
  unless unsafe_tor_rendezvous 0xDEADBEEF true true do
    throw (IO.userError "vuln: malicious rendezvous accepted")
  unless unsafe_tor_rendezvous 0x00000000 true false do
    throw (IO.userError "vuln: no-connect malicious accepted")
  unless unsafe_tor_rendezvous 0x7F000001 false false do
    throw (IO.userError "localhost honest rejected")
  IO.println "All tests passed."

#eval check

/-! ## Precondition -/

/-- The Python function imposes no restriction on its three typed arguments. -/
def Pre (_rendezvous_addr : Int) (_is_malicious _hidden_service_connects : Bool) : Prop :=
  True

/-! ## Behavioral properties and kernel-checked proofs -/

def always_accepts_prop (addr : Int) (malicious connects : Bool) : Prop :=
  unsafe_tor_rendezvous addr malicious connects = true

theorem always_accepts_thm (addr : Int) (malicious connects : Bool) :
    always_accepts_prop addr malicious connects := by
  rfl

def honest_accepted_prop (addr : Int) (connects : Bool) : Prop :=
  unsafe_tor_rendezvous addr false connects = true

theorem honest_accepted_thm (addr : Int) (connects : Bool) :
    honest_accepted_prop addr connects := by
  rfl

/-- In particular, an adversarial rendezvous is not rejected, even on connection. -/
def malicious_accepted_prop (addr : Int) (connects : Bool) : Prop :=
  unsafe_tor_rendezvous addr true connects = true

theorem malicious_accepted_thm (addr : Int) (connects : Bool) :
    malicious_accepted_prop addr connects := by
  rfl

/-- The source does not even require a hidden-service connection for acceptance. -/
def connection_not_required_prop (addr : Int) (malicious : Bool) : Prop :=
  unsafe_tor_rendezvous addr malicious false = true

theorem connection_not_required_thm (addr : Int) (malicious : Bool) :
    connection_not_required_prop addr malicious := by
  rfl

/-- Changing any or all of the inputs cannot change the result. -/
def input_independence_prop
    (addr other_addr : Int) (malicious connects other_malicious other_connects : Bool) : Prop :=
  unsafe_tor_rendezvous addr malicious connects =
    unsafe_tor_rendezvous other_addr other_malicious other_connects

theorem input_independence_thm
    (addr other_addr : Int) (malicious connects other_malicious other_connects : Bool) :
    input_independence_prop addr other_addr malicious connects other_malicious other_connects := by
  rfl

/-! ## Postcondition -/

/-- The exact output and the consequences of ignoring authentication and connection state. -/
def Post_prop (addr : Int) (malicious connects : Bool) : Prop :=
  always_accepts_prop addr malicious connects ∧
  honest_accepted_prop addr connects ∧
  malicious_accepted_prop addr connects ∧
  connection_not_required_prop addr malicious ∧
  (∀ (other_addr : Int) (other_malicious other_connects : Bool),
    input_independence_prop addr other_addr malicious connects other_malicious other_connects)

/-! ## Property-based tests

Each randomized test below checks executable equalities over the implementation,
not a theorem used as a test oracle. All inputs satisfy `Pre`, so no samples are
discarded. These tests are evidence only; the proofs above and below use `rfl`
or the proved lemmas, not the test results.
-/

-- PBT for always_accepts_prop.
#eval Plausible.Testable.check
  (∀ (addr : Int) (malicious connects : Bool),
    unsafe_tor_rendezvous addr malicious connects = true)

-- PBT for honest_accepted_prop.
#eval Plausible.Testable.check
  (∀ (addr : Int) (connects : Bool),
    unsafe_tor_rendezvous addr false connects = true)

-- PBT for malicious_accepted_prop, including both connection states.
#eval Plausible.Testable.check
  (∀ (addr : Int) (connects : Bool),
    unsafe_tor_rendezvous addr true connects = true)

-- PBT for connection_not_required_prop, including both maliciousness states.
#eval Plausible.Testable.check
  (∀ (addr : Int) (malicious : Bool),
    unsafe_tor_rendezvous addr malicious false = true)

-- PBT for input_independence_prop: independently vary all six inputs.
#eval Plausible.Testable.check
  (∀ (addr other_addr : Int) (malicious connects other_malicious other_connects : Bool),
    unsafe_tor_rendezvous addr malicious connects =
      unsafe_tor_rendezvous other_addr other_malicious other_connects)

-- PBT for Post_prop. Its inner universal is exposed as more sampled arguments;
-- the conjunction is the executable form of every component of the postcondition.
#eval Plausible.Testable.check
  (∀ (addr other_addr : Int) (malicious connects other_malicious other_connects : Bool),
    unsafe_tor_rendezvous addr malicious connects = true ∧
    unsafe_tor_rendezvous addr false connects = true ∧
    unsafe_tor_rendezvous addr true connects = true ∧
    unsafe_tor_rendezvous addr malicious false = true ∧
    unsafe_tor_rendezvous addr malicious connects =
      unsafe_tor_rendezvous other_addr other_malicious other_connects)

-- Additional bounded PBT: all addresses from -32 through 32, and all flag pairs.
example :
    (List.range 65).all (fun n =>
      [false, true].all (fun malicious =>
        [false, true].all (fun connects =>
          unsafe_tor_rendezvous ((n : Int) - 32) malicious connects))) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (addr : Int) (malicious connects : Bool) :
    Pre addr malicious connects → Post_prop addr malicious connects := by
  intro _
  refine ⟨always_accepts_thm addr malicious connects,
    honest_accepted_thm addr connects,
    malicious_accepted_thm addr connects,
    connection_not_required_thm addr malicious, ?_⟩
  intro other_addr other_malicious other_connects
  exact input_independence_thm addr other_addr malicious connects other_malicious other_connects

/-! ## Imperative implementation -/

/-- A local mutable result is unconditionally set to true, with no authentication. -/
def unsafe_tor_rendezvous_imperative
    (_rendezvous_addr : Int) (_is_malicious _hidden_service_connects : Bool) : Bool := Id.run do
  let mut accepted : Bool := false
  accepted := true
  return accepted

/-! ## Imperative tests -/

example : unsafe_tor_rendezvous_imperative 0x0A000001 false true = true := by native_decide
example : unsafe_tor_rendezvous_imperative 0xDEADBEEF true true = true := by native_decide
example : unsafe_tor_rendezvous_imperative 0x00000000 true false = true := by native_decide
example : unsafe_tor_rendezvous_imperative 0x7F000001 false false = true := by native_decide

#eval [unsafe_tor_rendezvous_imperative 0x0A000001 false true,
       unsafe_tor_rendezvous_imperative 0xDEADBEEF true true,
       unsafe_tor_rendezvous_imperative 0x00000000 true false,
       unsafe_tor_rendezvous_imperative 0x7F000001 false false]

/-! ## Functional / imperative equivalence -/

theorem functional_imperative_equivalence_thm
    (addr : Int) (malicious connects : Bool) :
    unsafe_tor_rendezvous addr malicious connects =
      unsafe_tor_rendezvous_imperative addr malicious connects := by
  rfl

end UnsafeTorHiddenService
end Agent
