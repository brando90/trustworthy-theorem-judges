import Mathlib
import Plausible

/-!
# VeriBench 129 — Unsafe Tor Hidden-Service Rendezvous

Translation of a Python function that models an **unsafe** Tor hidden-service
rendezvous. The hidden service does not authenticate or vet the rendezvous
point: the procedure returns `true` for every address and every combination of
the malicious-operator and connection flags.

Vulnerability (MIT 6.858 Fall 2012 Quiz 2): a malicious Tor onion router can
set up a rendezvous point on itself and advertise that address through the
introduction point. When the hidden service connects, the malicious node
records the origin of the incoming connection and deanonymizes the service.
Because this implementation never authenticates the rendezvous point, a
malicious rendezvous is accepted exactly like an honest one, whether or not
the hidden service actually connects.

The functional model, the imperative model, and every stated property follow
that Python behavior: acceptance is unconditional.
-/

namespace «129_unsafeTorHiddenService»

/-! ## Implementation -/

/--
Unsafe Tor hidden-service rendezvous.

Returns `true` regardless of whether the rendezvous point is controlled by an
adversary. The address, the malicious-operator flag, and the
hidden-service-connects flag are all ignored: the rendezvous is never
authenticated or vetted.

* `rendezvousAddr` — advertised rendezvous address (Python `int`).
* `isMalicious` — `true` when an adversary controls the rendezvous point.
* `hiddenServiceConnects` — `true` when the hidden service opens the connection.
-/
def unsafe_tor_rendezvous (rendezvousAddr : Int) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) : Bool :=
  let _addr := rendezvousAddr
  let _malicious := isMalicious
  let _connects := hiddenServiceConnects
  -- Vulnerable: rendezvous never authenticated.
  true

/-! ## Unit tests -/

-- honest rendezvous rejected? No: the unsafe procedure accepts it.
example : unsafe_tor_rendezvous (0x0A000001 : Int) false true = true := by
  native_decide

-- vuln: malicious rendezvous accepted
example : unsafe_tor_rendezvous (0xDEADBEEF : Int) true true = true := by
  native_decide

-- vuln: no-connect malicious accepted
example : unsafe_tor_rendezvous (0x00000000 : Int) true false = true := by
  native_decide

-- localhost honest rejected? No: still accepted.
example : unsafe_tor_rendezvous (0x7F000001 : Int) false false = true := by
  native_decide

#eval unsafe_tor_rendezvous (0x0A000001 : Int) false true
#eval unsafe_tor_rendezvous (0xDEADBEEF : Int) true true
#eval unsafe_tor_rendezvous (0x00000000 : Int) true false
#eval unsafe_tor_rendezvous (0x7F000001 : Int) false false

/-! ## Pre-condition -/

/--
Every Python `int` address and every pair of flags is an admissible input.
The implementation performs no validation, so the precondition does not
restrict the domain.
-/
def Pre (rendezvousAddr : Int) (isMalicious : Bool) (hiddenServiceConnects : Bool) : Prop :=
  -- Inputs are total; the marks keep every parameter in the predicate.
  rendezvousAddr = rendezvousAddr ∧
    isMalicious = isMalicious ∧
    hiddenServiceConnects = hiddenServiceConnects

/-! ## Properties -/

/-- The procedure returns `true` for every input (rendezvous never authenticated). -/
def always_returns_true_prop (rendezvousAddr : Int) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvousAddr isMalicious hiddenServiceConnects = true

theorem always_returns_true_thm (rendezvousAddr : Int) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) :
    always_returns_true_prop rendezvousAddr isMalicious hiddenServiceConnects := by
  unfold always_returns_true_prop unsafe_tor_rendezvous
  rfl

/--
Vulnerability: a malicious rendezvous point is accepted. A vetted implementation
would reject `isMalicious = true`; this one does not.
-/
def malicious_rendezvous_accepted_prop (rendezvousAddr : Int)
    (hiddenServiceConnects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvousAddr true hiddenServiceConnects = true

theorem malicious_rendezvous_accepted_thm (rendezvousAddr : Int)
    (hiddenServiceConnects : Bool) :
    malicious_rendezvous_accepted_prop rendezvousAddr hiddenServiceConnects := by
  unfold malicious_rendezvous_accepted_prop unsafe_tor_rendezvous
  rfl

/-- An honest rendezvous point is also accepted (the procedure does not distinguish). -/
def honest_rendezvous_accepted_prop (rendezvousAddr : Int)
    (hiddenServiceConnects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvousAddr false hiddenServiceConnects = true

theorem honest_rendezvous_accepted_thm (rendezvousAddr : Int)
    (hiddenServiceConnects : Bool) :
    honest_rendezvous_accepted_prop rendezvousAddr hiddenServiceConnects := by
  unfold honest_rendezvous_accepted_prop unsafe_tor_rendezvous
  rfl

/--
Attack path from the docstring: the hidden service connects to a rendezvous
point controlled by an adversary, and the connection is still accepted, so the
malicious node can record the origin and deanonymize the service.
-/
def deanonymization_path_accepted_prop (rendezvousAddr : Int) : Prop :=
  unsafe_tor_rendezvous rendezvousAddr true true = true

theorem deanonymization_path_accepted_thm (rendezvousAddr : Int) :
    deanonymization_path_accepted_prop rendezvousAddr := by
  unfold deanonymization_path_accepted_prop unsafe_tor_rendezvous
  rfl

/-- A malicious rendezvous is accepted even when the hidden service does not connect. -/
def no_connect_malicious_accepted_prop (rendezvousAddr : Int) : Prop :=
  unsafe_tor_rendezvous rendezvousAddr true false = true

theorem no_connect_malicious_accepted_thm (rendezvousAddr : Int) :
    no_connect_malicious_accepted_prop rendezvousAddr := by
  unfold no_connect_malicious_accepted_prop unsafe_tor_rendezvous
  rfl

/-- Acceptance does not depend on whether the rendezvous operator is malicious. -/
def ignores_malicious_flag_prop (rendezvousAddr : Int) (mal1 mal2 : Bool)
    (hiddenServiceConnects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvousAddr mal1 hiddenServiceConnects =
    unsafe_tor_rendezvous rendezvousAddr mal2 hiddenServiceConnects

theorem ignores_malicious_flag_thm (rendezvousAddr : Int) (mal1 mal2 : Bool)
    (hiddenServiceConnects : Bool) :
    ignores_malicious_flag_prop rendezvousAddr mal1 mal2 hiddenServiceConnects := by
  unfold ignores_malicious_flag_prop unsafe_tor_rendezvous
  rfl

/-- Acceptance does not depend on whether the hidden service connects. -/
def ignores_connection_flag_prop (rendezvousAddr : Int) (isMalicious : Bool)
    (c1 c2 : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvousAddr isMalicious c1 =
    unsafe_tor_rendezvous rendezvousAddr isMalicious c2

theorem ignores_connection_flag_thm (rendezvousAddr : Int) (isMalicious : Bool)
    (c1 c2 : Bool) :
    ignores_connection_flag_prop rendezvousAddr isMalicious c1 c2 := by
  unfold ignores_connection_flag_prop unsafe_tor_rendezvous
  rfl

/-- Acceptance does not depend on the advertised rendezvous address. -/
def ignores_address_prop (addr1 addr2 : Int) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) : Prop :=
  unsafe_tor_rendezvous addr1 isMalicious hiddenServiceConnects =
    unsafe_tor_rendezvous addr2 isMalicious hiddenServiceConnects

theorem ignores_address_thm (addr1 addr2 : Int) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) :
    ignores_address_prop addr1 addr2 isMalicious hiddenServiceConnects := by
  unfold ignores_address_prop unsafe_tor_rendezvous
  rfl

/--
The concrete quiz vectors: honest `10.0.0.1` with a connection, malicious
`0xDEADBEEF` with a connection, malicious `0.0.0.0` without a connection, and
honest localhost `127.0.0.1` without a connection are all accepted.
-/
def quiz_vectors_accepted_prop : Prop :=
  unsafe_tor_rendezvous (0x0A000001 : Int) false true = true ∧
    unsafe_tor_rendezvous (0xDEADBEEF : Int) true true = true ∧
    unsafe_tor_rendezvous (0x00000000 : Int) true false = true ∧
    unsafe_tor_rendezvous (0x7F000001 : Int) false false = true

theorem quiz_vectors_accepted_thm : quiz_vectors_accepted_prop := by
  unfold quiz_vectors_accepted_prop unsafe_tor_rendezvous
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Post-condition -/

/--
Post-condition: the call accepts unconditionally. This is the conjunction of
the behavioral properties at the given inputs — always-true result, malicious
and honest acceptance, the deanonymization path, the no-connect malicious
case, and independence from the malicious flag, the connection flag, and the
address.
-/
def Post_prop (rendezvousAddr : Int) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) : Prop :=
  always_returns_true_prop rendezvousAddr isMalicious hiddenServiceConnects ∧
    malicious_rendezvous_accepted_prop rendezvousAddr hiddenServiceConnects ∧
    honest_rendezvous_accepted_prop rendezvousAddr hiddenServiceConnects ∧
    deanonymization_path_accepted_prop rendezvousAddr ∧
    no_connect_malicious_accepted_prop rendezvousAddr ∧
    ignores_malicious_flag_prop rendezvousAddr isMalicious (!isMalicious)
      hiddenServiceConnects ∧
    ignores_connection_flag_prop rendezvousAddr isMalicious hiddenServiceConnects
      (!hiddenServiceConnects) ∧
    ignores_address_prop rendezvousAddr (rendezvousAddr + 1) isMalicious
      hiddenServiceConnects ∧
    quiz_vectors_accepted_prop

/-! ## Property-based tests -/

-- PBT: always_returns_true_prop
#eval Plausible.Testable.check
  (∀ (addr : Int) (mal conn : Bool),
    unsafe_tor_rendezvous addr mal conn = true)

-- PBT: malicious_rendezvous_accepted_prop
#eval Plausible.Testable.check
  (∀ (addr : Int) (conn : Bool),
    unsafe_tor_rendezvous addr true conn = true)

-- PBT: honest_rendezvous_accepted_prop
#eval Plausible.Testable.check
  (∀ (addr : Int) (conn : Bool),
    unsafe_tor_rendezvous addr false conn = true)

-- PBT: deanonymization_path_accepted_prop
#eval Plausible.Testable.check
  (∀ addr : Int, unsafe_tor_rendezvous addr true true = true)

-- PBT: no_connect_malicious_accepted_prop
#eval Plausible.Testable.check
  (∀ addr : Int, unsafe_tor_rendezvous addr true false = true)

-- PBT: ignores_malicious_flag_prop
#eval Plausible.Testable.check
  (∀ (addr : Int) (mal1 mal2 conn : Bool),
    unsafe_tor_rendezvous addr mal1 conn = unsafe_tor_rendezvous addr mal2 conn)

-- PBT: ignores_connection_flag_prop
#eval Plausible.Testable.check
  (∀ (addr : Int) (mal : Bool) (c1 c2 : Bool),
    unsafe_tor_rendezvous addr mal c1 = unsafe_tor_rendezvous addr mal c2)

-- PBT: ignores_address_prop
#eval Plausible.Testable.check
  (∀ (a1 a2 : Int) (mal conn : Bool),
    unsafe_tor_rendezvous a1 mal conn = unsafe_tor_rendezvous a2 mal conn)

-- PBT: quiz_vectors_accepted_prop (executable Boolean form of the four quiz vectors)
#eval Plausible.Testable.check
  (unsafe_tor_rendezvous (0x0A000001 : Int) false true = true ∧
    unsafe_tor_rendezvous (0xDEADBEEF : Int) true true = true ∧
    unsafe_tor_rendezvous (0x00000000 : Int) true false = true ∧
    unsafe_tor_rendezvous (0x7F000001 : Int) false false = true)

-- PBT: Post_prop over random inputs (executable Boolean form of the conjunction)
#eval Plausible.Testable.check
  (∀ (addr : Int) (mal conn : Bool),
    unsafe_tor_rendezvous addr mal conn = true ∧
      unsafe_tor_rendezvous addr true conn = true ∧
      unsafe_tor_rendezvous addr false conn = true ∧
      unsafe_tor_rendezvous addr true true = true ∧
      unsafe_tor_rendezvous addr true false = true ∧
      unsafe_tor_rendezvous addr mal conn =
        unsafe_tor_rendezvous addr (!mal) conn ∧
      unsafe_tor_rendezvous addr mal conn =
        unsafe_tor_rendezvous addr mal (!conn) ∧
      unsafe_tor_rendezvous addr mal conn =
        unsafe_tor_rendezvous (addr + 1) mal conn ∧
      unsafe_tor_rendezvous (0x0A000001 : Int) false true = true ∧
      unsafe_tor_rendezvous (0xDEADBEEF : Int) true true = true ∧
      unsafe_tor_rendezvous (0x00000000 : Int) true false = true ∧
      unsafe_tor_rendezvous (0x7F000001 : Int) false false = true)

-- Bounded PBTs: exhaustive small addresses, including the sign of `Int`.
example :
    (List.range 32).all (fun n =>
      unsafe_tor_rendezvous (n : Int) false true = true &&
      unsafe_tor_rendezvous (n : Int) true true = true &&
      unsafe_tor_rendezvous (n : Int) true false = true &&
      unsafe_tor_rendezvous (n : Int) false false = true) = true := by
  native_decide

example :
    ([(-8 : Int), -1, 0, 1, 0x0A000001, 0x7F000001, 0xDEADBEEF]).all (fun addr =>
      unsafe_tor_rendezvous addr false true = true &&
      unsafe_tor_rendezvous addr true true = true &&
      unsafe_tor_rendezvous addr true false = true &&
      unsafe_tor_rendezvous addr false false = true) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (rendezvousAddr : Int) (isMalicious : Bool)
    (hiddenServiceConnects : Bool)
    (hPre : Pre rendezvousAddr isMalicious hiddenServiceConnects) :
    Post_prop rendezvousAddr isMalicious hiddenServiceConnects := by
  -- Every input is admissible; consume the precondition explicitly.
  rcases hPre with ⟨_hAddr, _hMal, _hConn⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact always_returns_true_thm rendezvousAddr isMalicious hiddenServiceConnects
  · exact malicious_rendezvous_accepted_thm rendezvousAddr hiddenServiceConnects
  · exact honest_rendezvous_accepted_thm rendezvousAddr hiddenServiceConnects
  · exact deanonymization_path_accepted_thm rendezvousAddr
  · exact no_connect_malicious_accepted_thm rendezvousAddr
  · exact ignores_malicious_flag_thm rendezvousAddr isMalicious (!isMalicious)
      hiddenServiceConnects
  · exact ignores_connection_flag_thm rendezvousAddr isMalicious
      hiddenServiceConnects (!hiddenServiceConnects)
  · exact ignores_address_thm rendezvousAddr (rendezvousAddr + 1) isMalicious
      hiddenServiceConnects
  · exact quiz_vectors_accepted_thm

/-! ## Imperative implementation -/

/--
Imperative counterpart of `unsafe_tor_rendezvous`.

Mutable state records the advertised address and both flags, then sets the
acceptance bit to `true` without ever consulting those observations. That is
the same missing authentication as the functional version.
-/
def unsafe_tor_rendezvous_imp (rendezvousAddr : Int) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) : Bool :=
  Id.run do
    let mut accepted : Bool := false
    -- Observations are stored so every input participates in the imperative
    -- state, then ignored: the rendezvous point is never authenticated.
    let mut _observedAddr : Int := rendezvousAddr
    let mut _observedMalicious : Bool := isMalicious
    let mut _observedConnects : Bool := hiddenServiceConnects
    accepted := true
    _observedAddr := _observedAddr
    _observedMalicious := _observedMalicious
    _observedConnects := _observedConnects
    return accepted

/-! ## Imperative tests -/

example : unsafe_tor_rendezvous_imp (0x0A000001 : Int) false true = true := by
  native_decide

example : unsafe_tor_rendezvous_imp (0xDEADBEEF : Int) true true = true := by
  native_decide

example : unsafe_tor_rendezvous_imp (0x00000000 : Int) true false = true := by
  native_decide

example : unsafe_tor_rendezvous_imp (0x7F000001 : Int) false false = true := by
  native_decide

#eval unsafe_tor_rendezvous_imp (0x0A000001 : Int) false true
#eval unsafe_tor_rendezvous_imp (0xDEADBEEF : Int) true true
#eval unsafe_tor_rendezvous_imp (0x00000000 : Int) true false
#eval unsafe_tor_rendezvous_imp (0x7F000001 : Int) false false

/-! ## Equivalence -/

/-- The functional and imperative implementations agree on every input. -/
theorem equivalence_thm (rendezvousAddr : Int) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) :
    unsafe_tor_rendezvous rendezvousAddr isMalicious hiddenServiceConnects =
      unsafe_tor_rendezvous_imp rendezvousAddr isMalicious hiddenServiceConnects := by
  -- Both sides reduce to `true`: the functional body is the constant `true`,
  -- and the imperative `Id.run` block assigns `accepted := true`.
  delta unsafe_tor_rendezvous unsafe_tor_rendezvous_imp Id.run
  rfl

end «129_unsafeTorHiddenService»
