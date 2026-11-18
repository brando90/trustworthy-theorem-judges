import Mathlib
namespace Agent

/-!
# Unsafe static key exchange

An abstract model of static-RSA TLS from MIT 6.858 Lecture 14: compromise of
its long-term key makes recorded past sessions decryptable. The model takes
only the compromise flag; it models neither ciphertexts nor cryptographic
operations. Past-session decryptability is exactly that flag.

The five assertions in the Python checker are preserved below, including its
repeated negative-path assertion. Both Boolean inputs are admissible. Bounded
property-based tests exhaust the entire input domain, whereas the named
proofs use kernel-checked reasoning independently of those tests.
-/

namespace UnsafeStaticKeyExchange

/-- Whether the attacker can decrypt past sessions. -/
def unsafeStaticKeyExchange (longTermKeyCompromised : Bool) : Bool :=
  longTermKeyCompromised

/-- Executable counterpart of the Python assertions: true iff all pass. -/
def check (candidate : Bool → Bool) : Bool :=
  (candidate true == true) &&
  (candidate false == false) &&
  (candidate true != candidate false) &&
  ([true, false].any (fun b => candidate b == true)) &&
  (candidate false == false)

-- Unit tests, including the Python check call.
example : unsafeStaticKeyExchange true = true := by native_decide
example : unsafeStaticKeyExchange false = false := by native_decide
example : unsafeStaticKeyExchange true ≠ unsafeStaticKeyExchange false := by
  native_decide
example : [true, false].any (fun b => unsafeStaticKeyExchange b == true) = true := by
  native_decide
example : check unsafeStaticKeyExchange = true := by native_decide

#eval unsafeStaticKeyExchange true
#eval unsafeStaticKeyExchange false
#eval check unsafeStaticKeyExchange
#eval if check unsafeStaticKeyExchange then "All tests passed." else "Candidate failed tests"

/-- There are no restrictions on the Boolean compromise flag. -/
def Pre (_longTermKeyCompromised : Bool) : Prop := True

/-- Python assertion 1: compromise reveals past sessions. -/
def compromise_prop : Prop := unsafeStaticKeyExchange true = true

theorem compromise_thm : compromise_prop := by
  rfl

/-- Python assertion 2: without compromise, past sessions remain safe. -/
def noCompromise_prop : Prop := unsafeStaticKeyExchange false = false

theorem noCompromise_thm : noCompromise_prop := by
  rfl

/-- Python assertion 3: the function is not constant. -/
def inputDependence_prop : Prop :=
  unsafeStaticKeyExchange true ≠ unsafeStaticKeyExchange false

theorem inputDependence_thm : inputDependence_prop := by
  change (true : Bool) ≠ false
  decide

/-- Python assertion 4: some Boolean input exposes past sessions. -/
def vulnerabilityWitness_prop : Prop :=
  ∃ b : Bool, unsafeStaticKeyExchange b = true

theorem vulnerabilityWitness_thm : vulnerabilityWitness_prop := by
  exact ⟨true, rfl⟩

/-- Python assertion 5, intentionally retaining the repeated negative path. -/
def negativePath_prop : Prop := unsafeStaticKeyExchange false = false

theorem negativePath_thm : negativePath_prop := by
  rfl

/-- The complete behavior, not merely the two ground examples. -/
def tracksKeyState_prop (longTermKeyCompromised : Bool) : Prop :=
  unsafeStaticKeyExchange longTermKeyCompromised = longTermKeyCompromised

theorem tracksKeyState_thm (longTermKeyCompromised : Bool) :
    tracksKeyState_prop longTermKeyCompromised := by
  rfl

/-- All five checks and exact behavior on the supplied input. -/
def Post_prop (longTermKeyCompromised : Bool) : Prop :=
  compromise_prop ∧
  noCompromise_prop ∧
  inputDependence_prop ∧
  vulnerabilityWitness_prop ∧
  negativePath_prop ∧
  tracksKeyState_prop longTermKeyCompromised

/-!
## Exhaustive bounded property-based tests

Boolean enumeration covers every admissible input. The fixed-input claims
are checked as implications over this enumeration; input dependence is
checked on every pair of distinct inputs. These are executable Boolean
checks, not Decidable instances or proofs used by the named theorems.
-/

-- PBT for compromise_prop: b = true implies that the result is true.
example : [true, false].all (fun b =>
    (b != true) || (unsafeStaticKeyExchange b == true)) = true := by
  native_decide

-- PBT for noCompromise_prop: b = false implies that the result is false.
example : [true, false].all (fun b =>
    (b != false) || (unsafeStaticKeyExchange b == false)) = true := by
  native_decide

-- PBT for inputDependence_prop: all distinct Boolean inputs differ in output.
example : [true, false].all (fun a =>
    [true, false].all (fun b =>
      (a == b) || (unsafeStaticKeyExchange a != unsafeStaticKeyExchange b))) = true := by
  native_decide

-- PBT for vulnerabilityWitness_prop: exhaustive search for its witness.
example : [true, false].any (fun b => unsafeStaticKeyExchange b == true) = true := by
  native_decide

-- PBT for negativePath_prop, separately retaining the fifth assertion.
example : [true, false].all (fun b =>
    (b != false) || (unsafeStaticKeyExchange b == false)) = true := by
  native_decide

-- PBT for tracksKeyState_prop: the full truth table is the identity table.
example : [true, false].all (fun b => unsafeStaticKeyExchange b == b) = true := by
  native_decide

-- PBT for Post_prop: check is exactly the first five Boolean conjuncts.
example : [true, false].all (fun b =>
    check unsafeStaticKeyExchange && (unsafeStaticKeyExchange b == b)) = true := by
  native_decide

/-- Every admissible input satisfies the complete specification. -/
theorem correctness_thm (longTermKeyCompromised : Bool) :
    Pre longTermKeyCompromised → Post_prop longTermKeyCompromised := by
  intro _
  exact ⟨compromise_thm, noCompromise_thm, inputDependence_thm,
    vulnerabilityWitness_thm, negativePath_thm,
    tracksKeyState_thm longTermKeyCompromised⟩

/-- The same information flow, expressed with mutable local state. -/
def unsafeStaticKeyExchangeImperative (longTermKeyCompromised : Bool) : Bool := Id.run do
  let mut pastSessionsDecryptable := false
  pastSessionsDecryptable := longTermKeyCompromised
  return pastSessionsDecryptable

-- Imperative unit tests and exhaustive comparison.
example : unsafeStaticKeyExchangeImperative true = true := by native_decide
example : unsafeStaticKeyExchangeImperative false = false := by native_decide
example : check unsafeStaticKeyExchangeImperative = true := by native_decide
example : [true, false].all (fun b =>
    unsafeStaticKeyExchange b == unsafeStaticKeyExchangeImperative b) = true := by
  native_decide

#eval unsafeStaticKeyExchangeImperative true
#eval unsafeStaticKeyExchangeImperative false
#eval check unsafeStaticKeyExchangeImperative

/-- Functional and imperative implementations agree on every Boolean input. -/
theorem functional_eq_imperative_thm (longTermKeyCompromised : Bool) :
    unsafeStaticKeyExchange longTermKeyCompromised =
      unsafeStaticKeyExchangeImperative longTermKeyCompromised := by
  rfl

end UnsafeStaticKeyExchange
end Agent
