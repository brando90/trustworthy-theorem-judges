import Mathlib
namespace Agent

/-!
# Unsafe U2F authentication with a client-supplied challenge

Translation of the MIT 6.858 Quiz 1 (Spring 2022), Question 2 Python
example. Python's unbounded integers are represented by `Int`. Verification
compares only the supplied signature and expected signature. Neither the
client challenge nor the server nonce influences the result. In particular,
this is a model of the deliberately unsafe verifier, not a cryptographic
signature algorithm or a repaired U2F protocol.

The specifications establish exact acceptance/rejection behavior, independence
from both ignored arguments, and replay even when the server nonce changes.
Fixed examples reproduce the Python assertions. Bounded property-based tests
also include negative integers; they are tests, not premises of the proofs.
-/

namespace UnsafeU2FChallenge

/-! ## Functional implementation -/

/-- The two ignored arguments remain in the API, exactly as in Python. -/
def unsafeU2FVerify
    (_client_challenge signature expected_signature _server_nonce : Int) : Bool :=
  decide (signature = expected_signature)

/-- Boolean aggregation of the four assertions in Python's `check` harness. -/
def check (candidate : Int → Int → Int → Int → Bool) : Bool :=
  candidate 42 0xDEAD 0xDEAD 99 &&
  candidate 7 0xBEEF 0xBEEF 9999 &&
  candidate 0 0 0 1 &&
  !(candidate 1 0xABCD 0x1234 1)

/-! ## Unit tests: normal operation, replay, zero, and a wrong signature -/

example : unsafeU2FVerify 42 0xDEAD 0xDEAD 99 = true := by native_decide
example : unsafeU2FVerify 7 0xBEEF 0xBEEF 9999 = true := by native_decide
example : unsafeU2FVerify 0 0 0 1 = true := by native_decide
example : unsafeU2FVerify 1 0xABCD 0x1234 1 = false := by native_decide
example : check unsafeU2FVerify = true := by native_decide

-- Python integers may also be negative.
example : unsafeU2FVerify (-42) (-7) (-7) (-99) = true := by native_decide
example : unsafeU2FVerify (-42) (-7) 7 (-99) = false := by native_decide

#eval unsafeU2FVerify 42 0xDEAD 0xDEAD 99
#eval unsafeU2FVerify 7 0xBEEF 0xBEEF 9999
#eval unsafeU2FVerify 0 0 0 1
#eval unsafeU2FVerify 1 0xABCD 0x1234 1
#eval check unsafeU2FVerify
#eval if check unsafeU2FVerify then "All tests passed." else "Candidate failed tests"

/-! ## Pre-condition -/

/-- Every integer quadruple is admissible; no freshness or equality is assumed. -/
def Pre (_client_challenge _signature _expected_signature _server_nonce : Int) : Prop :=
  True

/-! ## Properties and their kernel-checked proofs -/

/-- Acceptance is characterized exactly by signature equality. -/
def accepts_iff_prop (c s expected nonce : Int) : Prop :=
  unsafeU2FVerify c s expected nonce = true ↔ s = expected

theorem accepts_iff_thm (c s expected nonce : Int) :
    accepts_iff_prop c s expected nonce := by
  simp [accepts_iff_prop, unsafeU2FVerify]

/-- A wrong signature is rejected, even in this unsafe protocol. -/
def rejects_iff_prop (c s expected nonce : Int) : Prop :=
  unsafeU2FVerify c s expected nonce = false ↔ s ≠ expected

theorem rejects_iff_thm (c s expected nonce : Int) :
    rejects_iff_prop c s expected nonce := by
  simp [rejects_iff_prop, unsafeU2FVerify]

/-- Matching signatures are accepted for any challenge and server nonce. -/
def valid_signature_prop (c s nonce : Int) : Prop :=
  unsafeU2FVerify c s s nonce = true

theorem valid_signature_thm (c s nonce : Int) :
    valid_signature_prop c s nonce := by
  simp [valid_signature_prop, unsafeU2FVerify]

/-- The server nonce cannot affect either acceptance or rejection. -/
def nonce_ignored_prop (c s expected nonce₁ nonce₂ : Int) : Prop :=
  unsafeU2FVerify c s expected nonce₁ = unsafeU2FVerify c s expected nonce₂

theorem nonce_ignored_thm (c s expected nonce₁ nonce₂ : Int) :
    nonce_ignored_prop c s expected nonce₁ nonce₂ := by
  rfl

/-- Even the client challenge is unused by this simplified Python verifier. -/
def challenge_ignored_prop (c₁ c₂ s expected nonce : Int) : Prop :=
  unsafeU2FVerify c₁ s expected nonce = unsafeU2FVerify c₂ s expected nonce

theorem challenge_ignored_thm (c₁ c₂ s expected nonce : Int) :
    challenge_ignored_prop c₁ c₂ s expected nonce := by
  rfl

/-- An accepted recorded pair is accepted with every new server nonce.
No restriction is imposed on the new nonce, so genuinely fresh nonces are
included. As in Python, the expected signature is held fixed for the pair. -/
def replay_prop (oldChallenge recordedSignature expectedSignature oldNonce freshNonce : Int) :
    Prop :=
  unsafeU2FVerify oldChallenge recordedSignature expectedSignature oldNonce = true →
  unsafeU2FVerify oldChallenge recordedSignature expectedSignature freshNonce = true

theorem replay_thm (oldChallenge recordedSignature expectedSignature oldNonce freshNonce : Int) :
    replay_prop oldChallenge recordedSignature expectedSignature oldNonce freshNonce := by
  intro accepted
  exact accepted

/-- A mismatch between the challenge and nonce does not prevent acceptance. -/
def mismatched_nonce_prop (c s nonce : Int) : Prop :=
  c ≠ nonce → unsafeU2FVerify c s s nonce = true

theorem mismatched_nonce_thm (c s nonce : Int) :
    mismatched_nonce_prop c s nonce := by
  intro _
  exact valid_signature_thm c s nonce

/-- The zero-challenge/zero-signature edge case works with any nonce. -/
def zero_prop (nonce : Int) : Prop :=
  unsafeU2FVerify 0 0 0 nonce = true

theorem zero_thm (nonce : Int) : zero_prop nonce := by
  exact valid_signature_thm 0 0 nonce

/-! ## Post-condition -/

/-- Exact results together with the protocol's insecure invariances.
The universally quantified clauses describe alternative requests, not merely
the particular nonce and challenge supplied to the original call. -/
def Post_prop (c s expected nonce : Int) : Prop :=
  accepts_iff_prop c s expected nonce ∧
  rejects_iff_prop c s expected nonce ∧
  valid_signature_prop c s nonce ∧
  (∀ otherNonce : Int, nonce_ignored_prop c s expected nonce otherNonce) ∧
  (∀ otherChallenge : Int, challenge_ignored_prop c otherChallenge s expected nonce) ∧
  (∀ freshNonce : Int, replay_prop c s expected nonce freshNonce) ∧
  mismatched_nonce_prop c s nonce ∧
  zero_prop nonce

/-! ## Bounded property-based tests

Each test evaluates the executable formula of its named property on a full
Cartesian product of integers from -3 through 3. Equal and unequal signatures,
negative values, zero, and matching and mismatching nonces are all exercised.
The unbounded theorem domains above are unchanged. No test is used in a named
theorem's proof. The post-condition's universally quantified clauses are
checked by independently ranging over the alternative nonce and challenge.
-/

def pbtInputs : List Int := (List.range 7).map (fun n => (n : Int) - 3)

-- PBT for accepts_iff_prop.
example : (pbtInputs.all fun c =>
    pbtInputs.all fun s =>
    pbtInputs.all fun expected =>
    pbtInputs.all fun nonce =>
      decide (unsafeU2FVerify c s expected nonce = true ↔ s = expected)) = true := by
  native_decide

-- PBT for rejects_iff_prop.
example : (pbtInputs.all fun c =>
    pbtInputs.all fun s =>
    pbtInputs.all fun expected =>
    pbtInputs.all fun nonce =>
      decide (unsafeU2FVerify c s expected nonce = false ↔ s ≠ expected)) = true := by
  native_decide

-- PBT for valid_signature_prop.
example : (pbtInputs.all fun c =>
    pbtInputs.all fun s =>
    pbtInputs.all fun nonce =>
      unsafeU2FVerify c s s nonce) = true := by
  native_decide

-- PBT for nonce_ignored_prop.
example : (pbtInputs.all fun c =>
    pbtInputs.all fun s =>
    pbtInputs.all fun expected =>
    pbtInputs.all fun nonce₁ =>
    pbtInputs.all fun nonce₂ =>
      decide (unsafeU2FVerify c s expected nonce₁ =
        unsafeU2FVerify c s expected nonce₂)) = true := by
  native_decide

-- PBT for challenge_ignored_prop.
example : (pbtInputs.all fun c₁ =>
    pbtInputs.all fun c₂ =>
    pbtInputs.all fun s =>
    pbtInputs.all fun expected =>
    pbtInputs.all fun nonce =>
      decide (unsafeU2FVerify c₁ s expected nonce =
        unsafeU2FVerify c₂ s expected nonce)) = true := by
  native_decide

-- PBT for replay_prop, including every accepted pair in the bounded domain.
example : (pbtInputs.all fun c =>
    pbtInputs.all fun s =>
    pbtInputs.all fun expected =>
    pbtInputs.all fun oldNonce =>
    pbtInputs.all fun freshNonce =>
      decide (unsafeU2FVerify c s expected oldNonce = true →
        unsafeU2FVerify c s expected freshNonce = true)) = true := by
  native_decide

-- PBT for mismatched_nonce_prop: all mismatching cases are tested, not discarded.
example : (pbtInputs.all fun c =>
    pbtInputs.all fun s =>
    pbtInputs.all fun nonce =>
      decide (c ≠ nonce → unsafeU2FVerify c s s nonce = true)) = true := by
  native_decide

-- PBT for zero_prop.
example : (pbtInputs.all fun nonce => unsafeU2FVerify 0 0 0 nonce) = true := by
  native_decide

-- PBT for Post_prop: executable conjunction, with the universal clauses
-- instantiated at every alternative nonce/challenge in the same bounded domain.
example : (pbtInputs.all fun c =>
    pbtInputs.all fun s =>
    pbtInputs.all fun expected =>
    pbtInputs.all fun nonce =>
    pbtInputs.all fun otherNonce =>
    pbtInputs.all fun otherChallenge =>
      decide (
        (unsafeU2FVerify c s expected nonce = true ↔ s = expected) ∧
        (unsafeU2FVerify c s expected nonce = false ↔ s ≠ expected) ∧
        unsafeU2FVerify c s s nonce = true ∧
        unsafeU2FVerify c s expected nonce = unsafeU2FVerify c s expected otherNonce ∧
        unsafeU2FVerify c s expected nonce = unsafeU2FVerify otherChallenge s expected nonce ∧
        (unsafeU2FVerify c s expected nonce = true →
          unsafeU2FVerify c s expected otherNonce = true) ∧
        (c ≠ nonce → unsafeU2FVerify c s s nonce = true) ∧
        unsafeU2FVerify 0 0 0 nonce = true)) = true := by
  native_decide

/-! ## Correctness: no hypotheses are needed beyond the unrestricted Pre -/

theorem correctness_thm (c s expected nonce : Int) :
    Pre c s expected nonce → Post_prop c s expected nonce := by
  intro _
  exact ⟨accepts_iff_thm c s expected nonce,
    rejects_iff_thm c s expected nonce,
    valid_signature_thm c s nonce,
    (fun otherNonce => nonce_ignored_thm c s expected nonce otherNonce),
    (fun otherChallenge => challenge_ignored_thm c otherChallenge s expected nonce),
    (fun freshNonce => replay_thm c s expected nonce freshNonce),
    mismatched_nonce_thm c s nonce,
    zero_thm nonce⟩

/-! ## Imperative implementation -/

/-- A mutable Boolean records the outcome; the nonce remains deliberately unused. -/
def unsafeU2FVerifyImperative
    (_client_challenge signature expected_signature _server_nonce : Int) : Bool := Id.run do
  let mut accepted := false
  if signature = expected_signature then
    accepted := true
  return accepted

/-! ## Imperative tests -/

example : unsafeU2FVerifyImperative 42 0xDEAD 0xDEAD 99 = true := by native_decide
example : unsafeU2FVerifyImperative 7 0xBEEF 0xBEEF 9999 = true := by native_decide
example : unsafeU2FVerifyImperative 0 0 0 1 = true := by native_decide
example : unsafeU2FVerifyImperative 1 0xABCD 0x1234 1 = false := by native_decide
example : unsafeU2FVerifyImperative (-42) (-7) (-7) (-99) = true := by native_decide
example : check unsafeU2FVerifyImperative = true := by native_decide

#eval unsafeU2FVerifyImperative 42 0xDEAD 0xDEAD 99
#eval unsafeU2FVerifyImperative 7 0xBEEF 0xBEEF 9999
#eval unsafeU2FVerifyImperative 0 0 0 1
#eval unsafeU2FVerifyImperative 1 0xABCD 0x1234 1
#eval check unsafeU2FVerifyImperative

-- Additional bounded PBT of functional/imperative agreement.
example : (pbtInputs.all fun c =>
    pbtInputs.all fun s =>
    pbtInputs.all fun expected =>
    pbtInputs.all fun nonce =>
      decide (unsafeU2FVerify c s expected nonce =
        unsafeU2FVerifyImperative c s expected nonce)) = true := by
  native_decide

/-! ## Functional/imperative equivalence on all Python integer inputs -/

theorem functional_eq_imperative_thm (c s expected nonce : Int) :
    unsafeU2FVerify c s expected nonce = unsafeU2FVerifyImperative c s expected nonce := by
  by_cases h : s = expected <;>
    simp [unsafeU2FVerify, unsafeU2FVerifyImperative, h]

end UnsafeU2FChallenge
end Agent
