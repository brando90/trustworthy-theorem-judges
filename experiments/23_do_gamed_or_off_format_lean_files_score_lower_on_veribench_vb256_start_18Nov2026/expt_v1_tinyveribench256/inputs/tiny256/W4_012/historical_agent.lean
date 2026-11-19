import Mathlib
namespace Agent

/-!
# Safe sensor-to-enclave authentication

Translation of `safe_sensor_replay`: accept exactly when the sensor session
matches the enclave's current session and the fingerprint matches. Checking
session freshness prevents accepting an old-session replay even when its
fingerprint matches.

Python's arbitrary-precision integers are represented by `Int`; negative and
large session identifiers remain admissible. The bounded tests are executable
evidence, while the named theorems prove the properties for all inputs.
-/

namespace «59_unsafeSensorReplay_safe»

/-! ## Functional implementation -/

def safe_sensor_replay (sensor_session_id enclave_session_id : Int)
    (fingerprint_match : Bool) : Bool :=
  (sensor_session_id == enclave_session_id) && fingerprint_match

/-! ## Unit tests: the five assertions in the Python test harness -/

example : safe_sensor_replay 42 42 true = true := by native_decide
example : safe_sensor_replay 1 42 true = false := by native_decide
example : safe_sensor_replay 42 42 false = false := by native_decide
example : safe_sensor_replay 0 9999 true = false := by native_decide
example : safe_sensor_replay 0 42 false = false := by native_decide

#eval [safe_sensor_replay 42 42 true,
       safe_sensor_replay 1 42 true,
       safe_sensor_replay 42 42 false,
       safe_sensor_replay 0 9999 true,
       safe_sensor_replay 0 42 false]

/-! ## Unrestricted precondition -/

/-- The Python implementation accepts any pair of integers and any Boolean. -/
def Pre (_sensor_session_id _enclave_session_id : Int)
    (_fingerprint_match : Bool) : Prop := True

/-! ## Properties and kernel-checked proofs -/

/-- Acceptance is equivalent to both freshness and a matching fingerprint. -/
def acceptance_prop (sensor_session_id enclave_session_id : Int)
    (fingerprint_match : Bool) : Prop :=
  safe_sensor_replay sensor_session_id enclave_session_id fingerprint_match = true ↔
    sensor_session_id = enclave_session_id ∧ fingerprint_match = true

theorem acceptance_thm (sensor_session_id enclave_session_id : Int)
    (fingerprint_match : Bool) :
    acceptance_prop sensor_session_id enclave_session_id fingerprint_match := by
  by_cases h : sensor_session_id = enclave_session_id <;>
    simp [acceptance_prop, safe_sensor_replay, h]

/-- Every mismatched session is rejected, regardless of its fingerprint. -/
def replay_rejection_prop (sensor_session_id enclave_session_id : Int)
    (fingerprint_match : Bool) : Prop :=
  sensor_session_id ≠ enclave_session_id →
    safe_sensor_replay sensor_session_id enclave_session_id fingerprint_match = false

theorem replay_rejection_thm (sensor_session_id enclave_session_id : Int)
    (fingerprint_match : Bool) :
    replay_rejection_prop sensor_session_id enclave_session_id fingerprint_match := by
  intro h
  simp [safe_sensor_replay, h]

/-- A failed fingerprint is rejected, even in the current session. -/
def fingerprint_rejection_prop (sensor_session_id enclave_session_id : Int)
    (fingerprint_match : Bool) : Prop :=
  fingerprint_match = false →
    safe_sensor_replay sensor_session_id enclave_session_id fingerprint_match = false

theorem fingerprint_rejection_thm (sensor_session_id enclave_session_id : Int)
    (fingerprint_match : Bool) :
    fingerprint_rejection_prop sensor_session_id enclave_session_id fingerprint_match := by
  intro h
  simp [safe_sensor_replay, h]

/-- Fresh data with a matching fingerprint is always accepted. -/
def valid_acceptance_prop (sensor_session_id enclave_session_id : Int)
    (fingerprint_match : Bool) : Prop :=
  sensor_session_id = enclave_session_id → fingerprint_match = true →
    safe_sensor_replay sensor_session_id enclave_session_id fingerprint_match = true

theorem valid_acceptance_thm (sensor_session_id enclave_session_id : Int)
    (fingerprint_match : Bool) :
    valid_acceptance_prop sensor_session_id enclave_session_id fingerprint_match := by
  intro hs hf
  simp [safe_sensor_replay, hs, hf]

/-- Rejection occurs exactly when at least one authentication check fails. -/
def rejection_prop (sensor_session_id enclave_session_id : Int)
    (fingerprint_match : Bool) : Prop :=
  safe_sensor_replay sensor_session_id enclave_session_id fingerprint_match = false ↔
    sensor_session_id ≠ enclave_session_id ∨ fingerprint_match = false

theorem rejection_thm (sensor_session_id enclave_session_id : Int)
    (fingerprint_match : Bool) :
    rejection_prop sensor_session_id enclave_session_id fingerprint_match := by
  by_cases h : sensor_session_id = enclave_session_id <;>
    simp [rejection_prop, safe_sensor_replay, h]

/-! ## Postcondition -/

/-- All security and acceptance guarantees hold together. -/
def Post_prop (sensor_session_id enclave_session_id : Int)
    (fingerprint_match : Bool) : Prop :=
  acceptance_prop sensor_session_id enclave_session_id fingerprint_match ∧
  replay_rejection_prop sensor_session_id enclave_session_id fingerprint_match ∧
  fingerprint_rejection_prop sensor_session_id enclave_session_id fingerprint_match ∧
  valid_acceptance_prop sensor_session_id enclave_session_id fingerprint_match ∧
  rejection_prop sensor_session_id enclave_session_id fingerprint_match

/-! ## Bounded property-based tests

Exhaust the Cartesian product of the session sample with itself and both
fingerprint values. The sample includes every integer from -16 through 16,
the original tests' larger identifiers, negative counterparts, and integers
beyond the signed 64-bit range. These bounds apply only to testing, not to
any theorem or precondition. Each check below is a Boolean form of the named
property, evaluated over the implementation.
-/

def sessionSamples : List Int :=
  (List.range 33).map (fun n => (n : Int) - 16) ++
    [42, 9999, -9999, 100000000000000000000, -100000000000000000000]

def boundedPBT (check : Int → Int → Bool → Bool) : Bool :=
  sessionSamples.all (fun s =>
    sessionSamples.all (fun e =>
      [false, true].all (fun f => check s e f)))

-- PBT for acceptance_prop: Boolean equality expresses the equivalence.
example : boundedPBT (fun s e f =>
    safe_sensor_replay s e f == ((s == e) && f)) = true := by
  native_decide

-- PBT for replay_rejection_prop: mismatch implies a false result.
example : boundedPBT (fun s e f =>
    (s == e) || !(safe_sensor_replay s e f)) = true := by
  native_decide

-- PBT for fingerprint_rejection_prop: a false fingerprint implies rejection.
example : boundedPBT (fun s e f =>
    f || !(safe_sensor_replay s e f)) = true := by
  native_decide

-- PBT for valid_acceptance_prop: both checks passing implies acceptance.
example : boundedPBT (fun s e f =>
    !((s == e) && f) || safe_sensor_replay s e f) = true := by
  native_decide

-- PBT for rejection_prop: rejection iff a session or fingerprint check fails.
example : boundedPBT (fun s e f =>
    (safe_sensor_replay s e f == false) == (!(s == e) || !f)) = true := by
  native_decide

/-- Executable conjunction of all five clauses in Post_prop. -/
def postCheck (s e : Int) (f : Bool) : Bool :=
  let actual := safe_sensor_replay s e f
  let fresh := s == e
  (actual == (fresh && f)) &&
  (fresh || !actual) &&
  (f || !actual) &&
  (!(fresh && f) || actual) &&
  ((actual == false) == (!fresh || !f))

-- PBT for Post_prop, checking its complete conjunction on every sample.
example : boundedPBT postCheck = true := by native_decide
#eval boundedPBT postCheck

/-! ## Correctness: Pre implies Post -/

theorem correctness_thm (sensor_session_id enclave_session_id : Int)
    (fingerprint_match : Bool) :
    Pre sensor_session_id enclave_session_id fingerprint_match →
      Post_prop sensor_session_id enclave_session_id fingerprint_match := by
  intro _
  exact ⟨acceptance_thm sensor_session_id enclave_session_id fingerprint_match,
    replay_rejection_thm sensor_session_id enclave_session_id fingerprint_match,
    fingerprint_rejection_thm sensor_session_id enclave_session_id fingerprint_match,
    valid_acceptance_thm sensor_session_id enclave_session_id fingerprint_match,
    rejection_thm sensor_session_id enclave_session_id fingerprint_match⟩

/-! ## Imperative implementation

Start in the rejected state. Only consult the fingerprint to update that
state after verifying the session ID, as in Python's short-circuit `and`.
-/

def safe_sensor_replay_imperative (sensor_session_id enclave_session_id : Int)
    (fingerprint_match : Bool) : Bool := Id.run do
  let mut accepted := false
  if sensor_session_id == enclave_session_id then
    accepted := fingerprint_match
  return accepted

/-! ## Imperative tests -/

example : safe_sensor_replay_imperative 42 42 true = true := by native_decide
example : safe_sensor_replay_imperative 1 42 true = false := by native_decide
example : safe_sensor_replay_imperative 42 42 false = false := by native_decide
example : safe_sensor_replay_imperative 0 9999 true = false := by native_decide
example : safe_sensor_replay_imperative 0 42 false = false := by native_decide

#eval [safe_sensor_replay_imperative 42 42 true,
       safe_sensor_replay_imperative 1 42 true,
       safe_sensor_replay_imperative 42 42 false,
       safe_sensor_replay_imperative 0 9999 true,
       safe_sensor_replay_imperative 0 42 false]

-- An additional bounded cross-check of the two implementations.
example : boundedPBT (fun s e f =>
    safe_sensor_replay s e f == safe_sensor_replay_imperative s e f) = true := by
  native_decide

/-! ## Functional / imperative equivalence -/

theorem functional_eq_imperative_thm (sensor_session_id enclave_session_id : Int)
    (fingerprint_match : Bool) :
    safe_sensor_replay sensor_session_id enclave_session_id fingerprint_match =
      safe_sensor_replay_imperative sensor_session_id enclave_session_id fingerprint_match := by
  by_cases h : sensor_session_id = enclave_session_id <;>
    simp [safe_sensor_replay, safe_sensor_replay_imperative, h]

end «59_unsafeSensorReplay_safe»
end Agent
