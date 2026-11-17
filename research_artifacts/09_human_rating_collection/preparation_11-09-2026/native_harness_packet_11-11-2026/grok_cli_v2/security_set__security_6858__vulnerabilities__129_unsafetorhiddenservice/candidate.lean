import Mathlib

/-!
# Unsafe Tor hidden-service rendezvous

Translation of a Python program that models an unauthenticated Tor hidden-service
rendezvous. `unsafe_tor_rendezvous` returns `true` for every address and every
flag: the hidden service never authenticates or vets the rendezvous point.

Vulnerability (MIT 6.858 Fall 2012, Quiz 2): a malicious Tor onion router can
advertise itself as the rendezvous point. When the hidden service connects, that
router records the connection origin and deanonymizes the service. The decision
procedure below accepts that rendezvous anyway.

The address is a Python `int` (unbounded, signed), so the Lean model uses `Int`.
`is_malicious` and `hidden_service_connects` are Booleans. The result is a
Boolean acceptance bit.
-/

namespace «129_unsafeTorHiddenService»

/-- Unauthenticated Tor hidden-service rendezvous.

Returns `true` regardless of `rendezvous_addr`, `is_malicious`, and
`hidden_service_connects`. The parameters are intentionally discarded: a
malicious rendezvous is not rejected, and a missing hidden-service connection
does not change the result. -/
def unsafe_tor_rendezvous (rendezvous_addr : Int) (is_malicious : Bool)
    (hidden_service_connects : Bool) : Bool :=
  let _ignored := (rendezvous_addr, is_malicious, hidden_service_connects)
  true

/-- Python `check`: the four rendezvous vectors in the original tests. -/
def check : Bool :=
  (unsafe_tor_rendezvous 0x0A000001 false true == true) &&
  (unsafe_tor_rendezvous 0xDEADBEEF true true == true) &&
  (unsafe_tor_rendezvous 0x00000000 true false == true) &&
  (unsafe_tor_rendezvous 0x7F000001 false false == true)

/-- Same report as the Python `print` after `check`. -/
def checkMessage : String :=
  if check then "All tests passed." else "Tests failed."

/-! ## Unit tests

The four assertions from Python `check`, plus direct evaluation.
-/

-- Honest rendezvous 10.0.0.1 is accepted.
example : unsafe_tor_rendezvous 0x0A000001 false true = true := by native_decide

-- Vulnerability: a malicious rendezvous (`0xDEADBEEF`) is accepted.
example : unsafe_tor_rendezvous 0xDEADBEEF true true = true := by native_decide

-- Vulnerability: a malicious rendezvous is accepted even if the service does not connect.
example : unsafe_tor_rendezvous 0x00000000 true false = true := by native_decide

-- Localhost honest rendezvous is accepted even when the service does not connect.
example : unsafe_tor_rendezvous 0x7F000001 false false = true := by native_decide

example : check = true := by native_decide

#eval unsafe_tor_rendezvous 0x0A000001 false true
#eval unsafe_tor_rendezvous 0xDEADBEEF true true
#eval unsafe_tor_rendezvous 0x00000000 true false
#eval unsafe_tor_rendezvous 0x7F000001 false false
#eval check
#eval checkMessage

/-! ## Pre-condition

Python imposes no restriction on the address or the flags. Every `Int` and both
Booleans are admissible, including malicious rendezvous points.
-/

/-- Every address and both flags are admissible. There is no authentication guard. -/
def Pre (_rendezvous_addr : Int) (_is_malicious : Bool)
    (_hidden_service_connects : Bool) : Prop :=
  True

/-! ## Properties -/

/-- The rendezvous is accepted for these arguments. -/
def unconditionalAccept_prop (rendezvous_addr : Int) (is_malicious : Bool)
    (hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects = true

/-- Acceptance does not depend on the arguments: every rendezvous is accepted. -/
theorem unconditionalAccept_thm (rendezvous_addr : Int) (is_malicious : Bool)
    (hidden_service_connects : Bool) :
    unconditionalAccept_prop rendezvous_addr is_malicious hidden_service_connects := by
  unfold unconditionalAccept_prop unsafe_tor_rendezvous
  rfl

/-- A malicious rendezvous point is accepted for every address and connection flag.

This is the vulnerability: the hidden service does not reject an
adversary-controlled rendezvous. -/
def maliciousAccepted_prop (rendezvous_addr : Int) (hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr true hidden_service_connects = true

theorem maliciousAccepted_thm (rendezvous_addr : Int) (hidden_service_connects : Bool) :
    maliciousAccepted_prop rendezvous_addr hidden_service_connects := by
  unfold maliciousAccepted_prop unsafe_tor_rendezvous
  rfl

/-- An honest rendezvous point is accepted as well. -/
def honestAccepted_prop (rendezvous_addr : Int) (hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr false hidden_service_connects = true

theorem honestAccepted_thm (rendezvous_addr : Int) (hidden_service_connects : Bool) :
    honestAccepted_prop rendezvous_addr hidden_service_connects := by
  unfold honestAccepted_prop unsafe_tor_rendezvous
  rfl

/-- The result stays `true` when the hidden service does not connect.

Python asserts this for a malicious rendezvous (`0x00000000`) and for an honest
localhost rendezvous. -/
def noConnectAccepted_prop (rendezvous_addr : Int) (is_malicious : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr is_malicious false = true

theorem noConnectAccepted_thm (rendezvous_addr : Int) (is_malicious : Bool) :
    noConnectAccepted_prop rendezvous_addr is_malicious := by
  unfold noConnectAccepted_prop unsafe_tor_rendezvous
  rfl

/-- The acceptance bit does not depend on `is_malicious`.

The rendezvous is never authenticated: flipping the adversary flag does not
change the decision. -/
def independentOfMalice_prop (rendezvous_addr : Int) (hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr true hidden_service_connects =
    unsafe_tor_rendezvous rendezvous_addr false hidden_service_connects

theorem independentOfMalice_thm (rendezvous_addr : Int) (hidden_service_connects : Bool) :
    independentOfMalice_prop rendezvous_addr hidden_service_connects := by
  unfold independentOfMalice_prop unsafe_tor_rendezvous
  rfl

/-- The acceptance bit does not depend on the rendezvous address.

The address is not vetted: any two addresses produce the same decision. -/
def independentOfAddress_prop (addr₁ addr₂ : Int) (is_malicious : Bool)
    (hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous addr₁ is_malicious hidden_service_connects =
    unsafe_tor_rendezvous addr₂ is_malicious hidden_service_connects

theorem independentOfAddress_thm (addr₁ addr₂ : Int) (is_malicious : Bool)
    (hidden_service_connects : Bool) :
    independentOfAddress_prop addr₁ addr₂ is_malicious hidden_service_connects := by
  unfold independentOfAddress_prop unsafe_tor_rendezvous
  rfl

/-- The acceptance bit does not depend on whether the hidden service connects. -/
def independentOfConnection_prop (rendezvous_addr : Int) (is_malicious : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr is_malicious true =
    unsafe_tor_rendezvous rendezvous_addr is_malicious false

theorem independentOfConnection_thm (rendezvous_addr : Int) (is_malicious : Bool) :
    independentOfConnection_prop rendezvous_addr is_malicious := by
  unfold independentOfConnection_prop unsafe_tor_rendezvous
  rfl

/-- Every combination of the two flags is accepted at this address.

These are the four shapes exercised by Python `check`, stated for an arbitrary
address. -/
def allFlagCombinations_prop (rendezvous_addr : Int) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr false false = true ∧
    unsafe_tor_rendezvous rendezvous_addr false true = true ∧
    unsafe_tor_rendezvous rendezvous_addr true false = true ∧
    unsafe_tor_rendezvous rendezvous_addr true true = true

theorem allFlagCombinations_thm (rendezvous_addr : Int) :
    allFlagCombinations_prop rendezvous_addr := by
  unfold allFlagCombinations_prop unsafe_tor_rendezvous
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The deanonymizing configuration is accepted.

When the rendezvous is malicious and the hidden service connects, the
implementation still returns `true`. That is the MIT 6.858 condition under
which the malicious onion router observes the service's origin. The function
does not record the origin itself; it fails to refuse the connection that
makes the observation possible. -/
def deanonymizingAccept_prop (rendezvous_addr : Int) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr true true = true

theorem deanonymizingAccept_thm (rendezvous_addr : Int) :
    deanonymizingAccept_prop rendezvous_addr := by
  unfold deanonymizingAccept_prop unsafe_tor_rendezvous
  rfl

/-- The decision ignores every input at once. -/
def inputIrrelevant_prop (addr₁ addr₂ : Int) (mal₁ mal₂ conn₁ conn₂ : Bool) : Prop :=
  unsafe_tor_rendezvous addr₁ mal₁ conn₁ = unsafe_tor_rendezvous addr₂ mal₂ conn₂

theorem inputIrrelevant_thm (addr₁ addr₂ : Int) (mal₁ mal₂ conn₁ conn₂ : Bool) :
    inputIrrelevant_prop addr₁ addr₂ mal₁ mal₂ conn₁ conn₂ := by
  unfold inputIrrelevant_prop unsafe_tor_rendezvous
  rfl

/-- The four concrete Python assertions all hold. -/
def check_prop : Prop :=
  unsafe_tor_rendezvous 0x0A000001 false true = true ∧
    unsafe_tor_rendezvous 0xDEADBEEF true true = true ∧
    unsafe_tor_rendezvous 0x00000000 true false = true ∧
    unsafe_tor_rendezvous 0x7F000001 false false = true

theorem check_thm : check_prop := by
  unfold check_prop unsafe_tor_rendezvous
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `check` agrees with `check_prop`. -/
theorem check_bool_thm : check = true := by
  unfold check unsafe_tor_rendezvous
  rfl

/-- `check_prop` holds exactly when the Boolean `check` harness returns `true`. -/
theorem check_prop_iff_thm : check_prop ↔ check = true := by
  unfold check_prop check unsafe_tor_rendezvous
  constructor
  · intro _
    rfl
  · intro _
    exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Post-condition

Conjunction of the properties above, instantiated at the call's arguments.
Address independence is stated against address `0`; together with the universal
correctness theorem this says the decision does not depend on the address.
-/

def Post_prop (rendezvous_addr : Int) (is_malicious : Bool)
    (hidden_service_connects : Bool) : Prop :=
  unconditionalAccept_prop rendezvous_addr is_malicious hidden_service_connects ∧
    maliciousAccepted_prop rendezvous_addr hidden_service_connects ∧
    honestAccepted_prop rendezvous_addr hidden_service_connects ∧
    noConnectAccepted_prop rendezvous_addr is_malicious ∧
    independentOfMalice_prop rendezvous_addr hidden_service_connects ∧
    independentOfConnection_prop rendezvous_addr is_malicious ∧
    independentOfAddress_prop rendezvous_addr 0 is_malicious hidden_service_connects ∧
    allFlagCombinations_prop rendezvous_addr ∧
    deanonymizingAccept_prop rendezvous_addr ∧
    inputIrrelevant_prop rendezvous_addr 0 is_malicious false hidden_service_connects false ∧
    check_prop

/-! ## Property-based tests

Randomized checks use Plausible. Bounded checks exhaust small addresses and the
concrete vectors from `check`. A passing test is evidence, not a proof.
-/

-- PBT: unconditionalAccept_prop
#eval Plausible.Testable.check
  (∀ rendezvous_addr : Int, ∀ is_malicious hidden_service_connects : Bool,
    unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects = true)

example : (List.range 30).all (fun n =>
    unsafe_tor_rendezvous (n : Int) false true &&
    unsafe_tor_rendezvous (n : Int) true true &&
    unsafe_tor_rendezvous (n : Int) true false &&
    unsafe_tor_rendezvous (n : Int) false false) = true := by native_decide

-- PBT: maliciousAccepted_prop
#eval Plausible.Testable.check
  (∀ rendezvous_addr : Int, ∀ hidden_service_connects : Bool,
    unsafe_tor_rendezvous rendezvous_addr true hidden_service_connects = true)

example : (List.range 30).all (fun n =>
    unsafe_tor_rendezvous (n : Int) true false &&
    unsafe_tor_rendezvous (n : Int) true true) = true := by native_decide

-- PBT: honestAccepted_prop
#eval Plausible.Testable.check
  (∀ rendezvous_addr : Int, ∀ hidden_service_connects : Bool,
    unsafe_tor_rendezvous rendezvous_addr false hidden_service_connects = true)

example : (List.range 30).all (fun n =>
    unsafe_tor_rendezvous (n : Int) false false &&
    unsafe_tor_rendezvous (n : Int) false true) = true := by native_decide

-- PBT: noConnectAccepted_prop
#eval Plausible.Testable.check
  (∀ rendezvous_addr : Int, ∀ is_malicious : Bool,
    unsafe_tor_rendezvous rendezvous_addr is_malicious false = true)

example : (List.range 30).all (fun n =>
    unsafe_tor_rendezvous (n : Int) false false &&
    unsafe_tor_rendezvous (n : Int) true false) = true := by native_decide

-- PBT: independentOfMalice_prop
#eval Plausible.Testable.check
  (∀ rendezvous_addr : Int, ∀ hidden_service_connects : Bool,
    unsafe_tor_rendezvous rendezvous_addr true hidden_service_connects =
      unsafe_tor_rendezvous rendezvous_addr false hidden_service_connects)

example : (List.range 30).all (fun n =>
    (unsafe_tor_rendezvous (n : Int) true true ==
      unsafe_tor_rendezvous (n : Int) false true) &&
    (unsafe_tor_rendezvous (n : Int) true false ==
      unsafe_tor_rendezvous (n : Int) false false)) = true := by native_decide

-- PBT: independentOfAddress_prop
#eval Plausible.Testable.check
  (∀ addr₁ addr₂ : Int, ∀ is_malicious hidden_service_connects : Bool,
    unsafe_tor_rendezvous addr₁ is_malicious hidden_service_connects =
      unsafe_tor_rendezvous addr₂ is_malicious hidden_service_connects)

example : (List.range 16).all (fun i =>
    (List.range 16).all (fun j =>
      unsafe_tor_rendezvous (i : Int) true false ==
        unsafe_tor_rendezvous (j : Int) true false)) = true := by native_decide

-- PBT: independentOfConnection_prop
#eval Plausible.Testable.check
  (∀ rendezvous_addr : Int, ∀ is_malicious : Bool,
    unsafe_tor_rendezvous rendezvous_addr is_malicious true =
      unsafe_tor_rendezvous rendezvous_addr is_malicious false)

example : (List.range 30).all (fun n =>
    (unsafe_tor_rendezvous (n : Int) false true ==
      unsafe_tor_rendezvous (n : Int) false false) &&
    (unsafe_tor_rendezvous (n : Int) true true ==
      unsafe_tor_rendezvous (n : Int) true false)) = true := by native_decide

-- PBT: allFlagCombinations_prop
#eval Plausible.Testable.check
  (∀ rendezvous_addr : Int,
    unsafe_tor_rendezvous rendezvous_addr false false = true ∧
    unsafe_tor_rendezvous rendezvous_addr false true = true ∧
    unsafe_tor_rendezvous rendezvous_addr true false = true ∧
    unsafe_tor_rendezvous rendezvous_addr true true = true)

example : (List.range 30).all (fun n =>
    unsafe_tor_rendezvous (n : Int) false false &&
    unsafe_tor_rendezvous (n : Int) false true &&
    unsafe_tor_rendezvous (n : Int) true false &&
    unsafe_tor_rendezvous (n : Int) true true) = true := by native_decide

-- PBT: deanonymizingAccept_prop
#eval Plausible.Testable.check
  (∀ rendezvous_addr : Int, unsafe_tor_rendezvous rendezvous_addr true true = true)

example : (List.range 30).all (fun n =>
    unsafe_tor_rendezvous (n : Int) true true) = true := by native_decide

-- PBT: inputIrrelevant_prop
#eval Plausible.Testable.check
  (∀ addr₁ addr₂ : Int, ∀ mal₁ mal₂ conn₁ conn₂ : Bool,
    unsafe_tor_rendezvous addr₁ mal₁ conn₁ = unsafe_tor_rendezvous addr₂ mal₂ conn₂)

-- Addresses outside `List.range`, including the Python vectors, negatives, and a
-- value past 32 bits. The implementation does not mask the address to IPv4.
def addressSuite : List Int :=
  [0, 1, -1, 0x0A000001, 0xDEADBEEF, 0x00000000, 0x7F000001, 0xFFFFFFFF, 0x100000000, -2147483648]

example : addressSuite.all (fun addr =>
    unsafe_tor_rendezvous addr false false &&
    unsafe_tor_rendezvous addr false true &&
    unsafe_tor_rendezvous addr true false &&
    unsafe_tor_rendezvous addr true true) = true := by native_decide

example : addressSuite.all (fun addr₁ =>
    addressSuite.all (fun addr₂ =>
      unsafe_tor_rendezvous addr₁ true true ==
        unsafe_tor_rendezvous addr₂ false false)) = true := by native_decide

-- PBT: check_prop. The proposition is a closed conjunction of `Bool` equalities;
-- this is its executable form (`check` is the same four comparisons).
#eval Plausible.Testable.check
  (unsafe_tor_rendezvous 0x0A000001 false true = true ∧
    unsafe_tor_rendezvous 0xDEADBEEF true true = true ∧
    unsafe_tor_rendezvous 0x00000000 true false = true ∧
    unsafe_tor_rendezvous 0x7F000001 false false = true)

-- PBT: Post_prop, executable Boolean form of the conjunction
#eval Plausible.Testable.check
  (∀ rendezvous_addr : Int, ∀ is_malicious hidden_service_connects : Bool,
    unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects = true ∧
    unsafe_tor_rendezvous rendezvous_addr true hidden_service_connects = true ∧
    unsafe_tor_rendezvous rendezvous_addr false hidden_service_connects = true ∧
    unsafe_tor_rendezvous rendezvous_addr is_malicious false = true ∧
    unsafe_tor_rendezvous rendezvous_addr true hidden_service_connects =
      unsafe_tor_rendezvous rendezvous_addr false hidden_service_connects ∧
    unsafe_tor_rendezvous rendezvous_addr is_malicious true =
      unsafe_tor_rendezvous rendezvous_addr is_malicious false ∧
    unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects =
      unsafe_tor_rendezvous 0 is_malicious hidden_service_connects ∧
    unsafe_tor_rendezvous rendezvous_addr false false = true ∧
    unsafe_tor_rendezvous rendezvous_addr false true = true ∧
    unsafe_tor_rendezvous rendezvous_addr true false = true ∧
    unsafe_tor_rendezvous rendezvous_addr true true = true ∧
    unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects =
      unsafe_tor_rendezvous 0 false false ∧
    unsafe_tor_rendezvous 0x0A000001 false true = true ∧
    unsafe_tor_rendezvous 0xDEADBEEF true true = true ∧
    unsafe_tor_rendezvous 0x00000000 true false = true ∧
    unsafe_tor_rendezvous 0x7F000001 false false = true)

example : (List.range 20).all (fun n =>
    let addr : Int := n
    unsafe_tor_rendezvous addr false true &&
      unsafe_tor_rendezvous addr true true &&
      (unsafe_tor_rendezvous addr true false ==
        unsafe_tor_rendezvous 0 false false) &&
      (unsafe_tor_rendezvous addr false false ==
        unsafe_tor_rendezvous addr true true)) = true := by native_decide

/-! ## Correctness: Pre implies Post -/

theorem correctness_thm (rendezvous_addr : Int) (is_malicious : Bool)
    (hidden_service_connects : Bool)
    (hPre : Pre rendezvous_addr is_malicious hidden_service_connects) :
    Post_prop rendezvous_addr is_malicious hidden_service_connects := by
  cases hPre
  unfold Post_prop
  exact ⟨
    unconditionalAccept_thm rendezvous_addr is_malicious hidden_service_connects,
    maliciousAccepted_thm rendezvous_addr hidden_service_connects,
    honestAccepted_thm rendezvous_addr hidden_service_connects,
    noConnectAccepted_thm rendezvous_addr is_malicious,
    independentOfMalice_thm rendezvous_addr hidden_service_connects,
    independentOfConnection_thm rendezvous_addr is_malicious,
    independentOfAddress_thm rendezvous_addr 0 is_malicious hidden_service_connects,
    allFlagCombinations_thm rendezvous_addr,
    deanonymizingAccept_thm rendezvous_addr,
    inputIrrelevant_thm rendezvous_addr 0 is_malicious false hidden_service_connects false,
    check_thm⟩

/-! ## Imperative implementation

Same acceptance policy, written with `Id.run` and mutable cells. The cells hold
the offered address and flags and are never used to reject the rendezvous.
-/

def unsafe_tor_rendezvous_imp (rendezvous_addr : Int) (is_malicious : Bool)
    (hidden_service_connects : Bool) : Bool :=
  Id.run do
    let mut accepted : Bool := true
    -- Record the offered rendezvous, then do not authenticate it.
    let mut _addr : Int := rendezvous_addr
    let mut _malicious : Bool := is_malicious
    let mut _connects : Bool := hidden_service_connects
    accepted := true
    return accepted

def checkImp : Bool :=
  (unsafe_tor_rendezvous_imp 0x0A000001 false true == true) &&
  (unsafe_tor_rendezvous_imp 0xDEADBEEF true true == true) &&
  (unsafe_tor_rendezvous_imp 0x00000000 true false == true) &&
  (unsafe_tor_rendezvous_imp 0x7F000001 false false == true)

/-! ## Imperative tests -/

example : unsafe_tor_rendezvous_imp 0x0A000001 false true = true := by native_decide
example : unsafe_tor_rendezvous_imp 0xDEADBEEF true true = true := by native_decide
example : unsafe_tor_rendezvous_imp 0x00000000 true false = true := by native_decide
example : unsafe_tor_rendezvous_imp 0x7F000001 false false = true := by native_decide
example : checkImp = true := by native_decide

#eval unsafe_tor_rendezvous_imp 0x0A000001 false true
#eval unsafe_tor_rendezvous_imp 0xDEADBEEF true true
#eval unsafe_tor_rendezvous_imp 0x00000000 true false
#eval unsafe_tor_rendezvous_imp 0x7F000001 false false
#eval checkImp

example : (List.range 30).all (fun n =>
    unsafe_tor_rendezvous_imp (n : Int) false true &&
    unsafe_tor_rendezvous_imp (n : Int) true true &&
    unsafe_tor_rendezvous_imp (n : Int) true false &&
    unsafe_tor_rendezvous_imp (n : Int) false false) = true := by native_decide

/-- The imperative procedure also accepts every input. -/
theorem unsafe_tor_rendezvous_imp_accepts_thm (rendezvous_addr : Int) (is_malicious : Bool)
    (hidden_service_connects : Bool) :
    unsafe_tor_rendezvous_imp rendezvous_addr is_malicious hidden_service_connects = true := by
  unfold unsafe_tor_rendezvous_imp Id.run
  rfl

/-! ## Equivalence: functional = imperative -/

theorem equivalence_thm (rendezvous_addr : Int) (is_malicious : Bool)
    (hidden_service_connects : Bool) :
    unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects =
      unsafe_tor_rendezvous_imp rendezvous_addr is_malicious hidden_service_connects := by
  unfold unsafe_tor_rendezvous unsafe_tor_rendezvous_imp Id.run
  rfl

theorem check_equiv_thm : check = checkImp := by
  unfold check checkImp unsafe_tor_rendezvous unsafe_tor_rendezvous_imp Id.run
  rfl

-- PBT: functional and imperative implementations agree
#eval Plausible.Testable.check
  (∀ rendezvous_addr : Int, ∀ is_malicious hidden_service_connects : Bool,
    unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects =
      unsafe_tor_rendezvous_imp rendezvous_addr is_malicious hidden_service_connects)

example : (List.range 30).all (fun n =>
    (unsafe_tor_rendezvous (n : Int) false true ==
      unsafe_tor_rendezvous_imp (n : Int) false true) &&
    (unsafe_tor_rendezvous (n : Int) true true ==
      unsafe_tor_rendezvous_imp (n : Int) true true) &&
    (unsafe_tor_rendezvous (n : Int) true false ==
      unsafe_tor_rendezvous_imp (n : Int) true false) &&
    (unsafe_tor_rendezvous (n : Int) false false ==
      unsafe_tor_rendezvous_imp (n : Int) false false)) = true := by native_decide

end «129_unsafeTorHiddenService»
