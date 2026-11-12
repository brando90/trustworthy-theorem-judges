import Mathlib

/-!
# Unsafe Tor hidden-service rendezvous

Translation of the Python function `unsafe_tor_rendezvous` and its four checks.
The function always returns `true`: it neither authenticates the rendezvous
address nor inspects maliciousness or whether the hidden service connects.
Addresses use `Int`, preserving Python's unrestricted integer input domain.

These claims describe the vulnerability, not a security guarantee. In
particular, acceptance of a malicious rendezvous is unconditional. The source
program does not simulate network connections, recording origins, or disclosure
of a service's identity, so no such side effects are added to this model.
-/

namespace UnsafeTorHiddenService

/-- Functional translation: the rendezvous is never authenticated. -/
def unsafe_tor_rendezvous
    (_rendezvous_addr : Int) (_is_malicious _hidden_service_connects : Bool) : Bool :=
  true

-- The four fixed examples from Python's `check`.
example : unsafe_tor_rendezvous 0x0A000001 false true = true := by native_decide
example : unsafe_tor_rendezvous 0xDEADBEEF true true = true := by native_decide
example : unsafe_tor_rendezvous 0x00000000 true false = true := by native_decide
example : unsafe_tor_rendezvous 0x7F000001 false false = true := by native_decide

/-- Executable counterpart of Python's assertions and success message. -/
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

/-- Every integer address and both values of either flag are admissible. -/
def Pre (_rendezvous_addr : Int) (_is_malicious _hidden_service_connects : Bool) : Prop :=
  True

/-- Acceptance is unconditional, for all three inputs. -/
def always_accepts_prop (addr : Int) (malicious connects : Bool) : Prop :=
  unsafe_tor_rendezvous addr malicious connects = true

theorem always_accepts_thm (addr : Int) (malicious connects : Bool) :
    always_accepts_prop addr malicious connects := by
  rfl

/-- Honest rendezvous points are accepted, even without a connection. -/
def honest_accepted_prop (addr : Int) (connects : Bool) : Prop :=
  unsafe_tor_rendezvous addr false connects = true

theorem honest_accepted_thm (addr : Int) (connects : Bool) :
    honest_accepted_prop addr connects := by
  rfl

/-- The vulnerability: malicious rendezvous points are accepted as well. -/
def malicious_accepted_prop (addr : Int) (connects : Bool) : Prop :=
  unsafe_tor_rendezvous addr true connects = true

theorem malicious_accepted_thm (addr : Int) (connects : Bool) :
    malicious_accepted_prop addr connects := by
  rfl

/-- A connection is not required for the function to report acceptance. -/
def no_connection_accepted_prop (addr : Int) (malicious : Bool) : Prop :=
  unsafe_tor_rendezvous addr malicious false = true

theorem no_connection_accepted_thm (addr : Int) (malicious : Bool) :
    no_connection_accepted_prop addr malicious := by
  rfl

/-- Changing any or all inputs cannot affect the returned Boolean. -/
def input_independent_prop
    (addr : Int) (malicious connects : Bool)
    (otherAddr : Int) (otherMalicious otherConnects : Bool) : Prop :=
  unsafe_tor_rendezvous addr malicious connects =
    unsafe_tor_rendezvous otherAddr otherMalicious otherConnects

theorem input_independent_thm
    (addr : Int) (malicious connects : Bool)
    (otherAddr : Int) (otherMalicious otherConnects : Bool) :
    input_independent_prop addr malicious connects otherAddr otherMalicious otherConnects := by
  rfl

/-- The full behavior, including independence from every alternative input. -/
def Post_prop (addr : Int) (malicious connects : Bool) : Prop :=
  always_accepts_prop addr malicious connects ∧
  honest_accepted_prop addr connects ∧
  malicious_accepted_prop addr connects ∧
  no_connection_accepted_prop addr malicious ∧
  (∀ (otherAddr : Int) (otherMalicious otherConnects : Bool),
    input_independent_prop addr malicious connects otherAddr otherMalicious otherConnects)

/-!
## Bounded property-based tests

Exhaustively test all integers from -16 through 16 and both flags, supplemented
by the source's large addresses, a negative large address, and integers beyond
machine-word size. For relational properties both input triples are sampled.
These executable Boolean checks are evidence only; the theorems above and
below prove the unrestricted statements independently of these tests.
-/

private def sampleAddresses : List Int :=
  (List.range 33).map (fun n => (n : Int) - 16) ++
    [0x0A000001, 0xDEADBEEF, 0x7F000001, -(0xDEADBEEF : Int),
      (2 : Int) ^ 128, -((2 : Int) ^ 128)]

private def sampleFlags : List Bool := [false, true]

private def forAllSamples (p : Int → Bool → Bool → Bool) : Bool :=
  sampleAddresses.all fun addr =>
    sampleFlags.all fun malicious =>
      sampleFlags.all fun connects => p addr malicious connects

-- PBT for always_accepts_prop.
example : forAllSamples (fun addr malicious connects =>
    unsafe_tor_rendezvous addr malicious connects == true) = true := by
  native_decide

-- PBT for honest_accepted_prop.
example : forAllSamples (fun addr _ connects =>
    unsafe_tor_rendezvous addr false connects == true) = true := by
  native_decide

-- PBT for malicious_accepted_prop.
example : forAllSamples (fun addr _ connects =>
    unsafe_tor_rendezvous addr true connects == true) = true := by
  native_decide

-- PBT for no_connection_accepted_prop.
example : forAllSamples (fun addr malicious _ =>
    unsafe_tor_rendezvous addr malicious false == true) = true := by
  native_decide

-- PBT for input_independent_prop, checking all pairs of sampled triples.
example : forAllSamples (fun addr malicious connects =>
    forAllSamples (fun otherAddr otherMalicious otherConnects =>
      unsafe_tor_rendezvous addr malicious connects ==
        unsafe_tor_rendezvous otherAddr otherMalicious otherConnects)) = true := by
  native_decide

-- PBT for Post_prop: Boolean forms of every conjunct, with its universal
-- input-independence conjunct exhaustively checked on the second sample grid.
example : forAllSamples (fun addr malicious connects =>
    (unsafe_tor_rendezvous addr malicious connects == true) &&
    (unsafe_tor_rendezvous addr false connects == true) &&
    (unsafe_tor_rendezvous addr true connects == true) &&
    (unsafe_tor_rendezvous addr malicious false == true) &&
    (forAllSamples (fun otherAddr otherMalicious otherConnects =>
      unsafe_tor_rendezvous addr malicious connects ==
        unsafe_tor_rendezvous otherAddr otherMalicious otherConnects))) = true := by
  native_decide

/-- Correctness has no additional assumptions about the address or flags. -/
theorem correctness_thm (addr : Int) (malicious connects : Bool) :
    Pre addr malicious connects → Post_prop addr malicious connects := by
  intro _
  exact ⟨always_accepts_thm addr malicious connects,
    honest_accepted_thm addr connects,
    malicious_accepted_thm addr connects,
    no_connection_accepted_thm addr malicious,
    fun otherAddr otherMalicious otherConnects =>
      input_independent_thm addr malicious connects otherAddr otherMalicious otherConnects⟩

/-- Imperative translation: overwrite the mutable result with `true`. -/
def unsafe_tor_rendezvous_imperative
    (_rendezvous_addr : Int) (_is_malicious _hidden_service_connects : Bool) : Bool :=
  Id.run do
    let mut accepted := false
    accepted := true
    return accepted

-- Imperative versions of all four source tests.
example : unsafe_tor_rendezvous_imperative 0x0A000001 false true = true := by native_decide
example : unsafe_tor_rendezvous_imperative 0xDEADBEEF true true = true := by native_decide
example : unsafe_tor_rendezvous_imperative 0x00000000 true false = true := by native_decide
example : unsafe_tor_rendezvous_imperative 0x7F000001 false false = true := by native_decide

#eval [unsafe_tor_rendezvous_imperative 0x0A000001 false true,
  unsafe_tor_rendezvous_imperative 0xDEADBEEF true true,
  unsafe_tor_rendezvous_imperative 0x00000000 true false,
  unsafe_tor_rendezvous_imperative 0x7F000001 false false]

/-- The two implementations agree for every Python-domain input. -/
theorem functional_imperative_equivalence_thm
    (addr : Int) (malicious connects : Bool) :
    unsafe_tor_rendezvous addr malicious connects =
      unsafe_tor_rendezvous_imperative addr malicious connects := by
  rfl

end UnsafeTorHiddenService
