import Mathlib
namespace Agent

/-!
# Safe U2F authentication with a server-supplied nonce

Translation of the Python `safeU2FVerify` program. Python integers are modeled
by `Int`, so negative values and arbitrarily large integers remain admissible.
A request is accepted exactly when both the challenge and the signature match
their server-side expected values. In particular, a stale challenge is rejected
even if its signature matches. Nonce generation and cryptography are external
to this function; replay rejection assumes the current nonce differs from the
recorded challenge, rather than asserting that nonce reuse is impossible.

The file includes the four original checks, kernel-proved specifications,
exhaustive bounded property tests, and an equivalent mutable implementation.
-/

namespace SafeU2FChallenge

/-! ## Functional implementation -/

/-- Preserve the Python early-rejection branch and signature equality check. -/
def safeU2FVerify
    (client_challenge signature expected_signature server_nonce : Int) : Bool :=
  if client_challenge ≠ server_nonce then
    false
  else
    decide (signature = expected_signature)

/-! ## Unit tests -/

example : safeU2FVerify 42 0xDEAD 0xDEAD 42 = true := by native_decide
example : safeU2FVerify 7 0xBEEF 0xBEEF 9999 = false := by native_decide
example : safeU2FVerify 0 0 0 0 = true := by native_decide
example : safeU2FVerify 1 0xABCD 0x1234 1 = false := by native_decide

-- Signed inputs are part of the Python domain, not an excluded edge case.
example : safeU2FVerify (-7) (-123) (-123) (-7) = true := by native_decide
example : safeU2FVerify (-7) (-123) (-123) 7 = false := by native_decide
example : safeU2FVerify (-1) (-3) 3 (-1) = false := by native_decide

/-- Executable counterpart of the four assertions in Python's `check`. -/
def check (candidate : Int → Int → Int → Int → Bool) : Bool :=
  candidate 42 0xDEAD 0xDEAD 42 &&
  !(candidate 7 0xBEEF 0xBEEF 9999) &&
  candidate 0 0 0 0 &&
  !(candidate 1 0xABCD 0x1234 1)

example : check safeU2FVerify = true := by native_decide
#eval safeU2FVerify 42 0xDEAD 0xDEAD 42
#eval safeU2FVerify 7 0xBEEF 0xBEEF 9999
#eval safeU2FVerify 0 0 0 0
#eval safeU2FVerify 1 0xABCD 0x1234 1
#eval check safeU2FVerify

/-! ## Precondition -/

/-- The Python function is total on all four integer inputs. -/
def Pre (_client_challenge _signature _expected_signature _server_nonce : Int) : Prop :=
  True

/-! ## Semantic properties and kernel-checked proofs -/

/-- Acceptance requires, and is guaranteed by, both equality checks. -/
def acceptance_prop (c s e n : Int) : Prop :=
  safeU2FVerify c s e n = true ↔ c = n ∧ s = e

theorem acceptance_thm (c s e n : Int) : acceptance_prop c s e n := by
  by_cases hn : c = n <;> simp [acceptance_prop, safeU2FVerify, hn]

/-- Normal authentication succeeds whenever the challenge and signature match. -/
def matching_inputs_prop (c s e n : Int) : Prop :=
  c = n → s = e → safeU2FVerify c s e n = true

theorem matching_inputs_thm (c s e n : Int) : matching_inputs_prop c s e n := by
  unfold matching_inputs_prop
  intro hn hs
  simp [safeU2FVerify, hn, hs]

/-- A recorded stale challenge is rejected, regardless of its signature.
This includes replaying a signature that still equals the expected value. -/
def replay_blocked_prop (c s e n : Int) : Prop :=
  c ≠ n → safeU2FVerify c s e n = false

theorem replay_blocked_thm (c s e n : Int) : replay_blocked_prop c s e n := by
  unfold replay_blocked_prop
  intro hn
  simp [safeU2FVerify, hn]

/-- A wrong signature is rejected, including when the nonce matches. -/
def wrong_signature_prop (c s e n : Int) : Prop :=
  s ≠ e → safeU2FVerify c s e n = false

theorem wrong_signature_thm (c s e n : Int) : wrong_signature_prop c s e n := by
  unfold wrong_signature_prop
  intro hs
  by_cases hn : c = n <;> simp [safeU2FVerify, hn, hs]

/-- These are precisely all the rejection cases. -/
def rejection_prop (c s e n : Int) : Prop :=
  safeU2FVerify c s e n = false ↔ c ≠ n ∨ s ≠ e

theorem rejection_thm (c s e n : Int) : rejection_prop c s e n := by
  by_cases hn : c = n <;> by_cases hs : s = e <;>
    simp [rejection_prop, safeU2FVerify, hn, hs]

/-! ## Postcondition -/

/-- The complete contract, including both successful and unsuccessful requests. -/
def Post_prop (c s e n : Int) : Prop :=
  acceptance_prop c s e n ∧
  matching_inputs_prop c s e n ∧
  replay_blocked_prop c s e n ∧
  wrong_signature_prop c s e n ∧
  rejection_prop c s e n

/-! ## Property-based tests

Each bounded test exhausts all 11^4 quadruples from [-5, 5], including negative
inputs, zero, equalities and inequalities. Implication antecedents are therefore
exercised, rather than relying on rare matches from independent random samples.
The tests use executable expansions of the properties, not theorem instances.
These tests are evidence only; all general proofs above are kernel checked.
-/

def pbtIntegers : List Int :=
  (List.range 11).map (fun k => (k : Int) - 5)

def allInputs (p : Int → Int → Int → Int → Bool) : Bool :=
  pbtIntegers.all fun c =>
    pbtIntegers.all fun s =>
      pbtIntegers.all fun e =>
        pbtIntegers.all fun n => p c s e n

-- PBT for acceptance_prop.
example : allInputs (fun c s e n =>
    decide (safeU2FVerify c s e n = true ↔ c = n ∧ s = e)) = true := by
  native_decide

-- PBT for matching_inputs_prop.
example : allInputs (fun c s e n =>
    decide (c = n → s = e → safeU2FVerify c s e n = true)) = true := by
  native_decide

-- PBT for replay_blocked_prop, including s = e.
example : allInputs (fun c s e n =>
    decide (c ≠ n → safeU2FVerify c s e n = false)) = true := by
  native_decide

-- PBT for wrong_signature_prop, including c = n.
example : allInputs (fun c s e n =>
    decide (s ≠ e → safeU2FVerify c s e n = false)) = true := by
  native_decide

-- PBT for rejection_prop.
example : allInputs (fun c s e n =>
    decide (safeU2FVerify c s e n = false ↔ c ≠ n ∨ s ≠ e)) = true := by
  native_decide

/-- Executable expansion of the complete postcondition. -/
def postCheck (c s e n : Int) : Bool :=
  let result := safeU2FVerify c s e n
  decide (
    (result = true ↔ c = n ∧ s = e) ∧
    (c = n → s = e → result = true) ∧
    (c ≠ n → result = false) ∧
    (s ≠ e → result = false) ∧
    (result = false ↔ c ≠ n ∨ s ≠ e))

-- PBT for Post_prop (all inputs satisfy Pre).
example : allInputs postCheck = true := by native_decide
#eval allInputs postCheck

/-! ## Overall correctness -/

theorem correctness_thm (c s e n : Int) : Pre c s e n → Post_prop c s e n := by
  intro _
  exact ⟨acceptance_thm c s e n,
    matching_inputs_thm c s e n,
    replay_blocked_thm c s e n,
    wrong_signature_thm c s e n,
    rejection_thm c s e n⟩

/-! ## Imperative implementation -/

/-- A mutable Boolean and early return implement the same control flow. -/
def safeU2FVerifyImperative
    (client_challenge signature expected_signature server_nonce : Int) : Bool := Id.run do
  let mut result := false
  if client_challenge ≠ server_nonce then
    return result
  result := decide (signature = expected_signature)
  return result

/-! ## Imperative tests -/

example : safeU2FVerifyImperative 42 0xDEAD 0xDEAD 42 = true := by native_decide
example : safeU2FVerifyImperative 7 0xBEEF 0xBEEF 9999 = false := by native_decide
example : safeU2FVerifyImperative 0 0 0 0 = true := by native_decide
example : safeU2FVerifyImperative 1 0xABCD 0x1234 1 = false := by native_decide
example : safeU2FVerifyImperative (-7) (-123) (-123) (-7) = true := by native_decide
example : check safeU2FVerifyImperative = true := by native_decide
#eval check safeU2FVerifyImperative

-- An additional bounded comparison exercises both imperative branches.
example : allInputs (fun c s e n =>
    safeU2FVerify c s e n == safeU2FVerifyImperative c s e n) = true := by
  native_decide

/-! ## Functional / imperative equivalence -/

theorem functional_imperative_equivalence_thm (c s e n : Int) :
    safeU2FVerify c s e n = safeU2FVerifyImperative c s e n := by
  by_cases hn : c ≠ n <;>
    simp [safeU2FVerify, safeU2FVerifyImperative, hn]

end SafeU2FChallenge
end Agent
