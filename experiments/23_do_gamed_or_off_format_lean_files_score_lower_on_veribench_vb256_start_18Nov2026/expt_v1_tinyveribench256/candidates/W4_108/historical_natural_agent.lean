import Mathlib
namespace Agent

/-!
# Unsafe TLS heartbeat: trusting the claimed length

This file translates the Python `unsafe_heartbeat` function and its test harness.
The result is the claimed length, not a length checked against the payload.
Consequently, a claimed length larger than the payload describes an over-read;
this model records the returned byte count, not actual memory contents.

`Int` preserves Python's arbitrary-precision integer input domain. In particular,
nonnegative lengths are conventional, but the source does not enforce them, so
neither does `Pre`. The proofs characterize the vulnerability rather than repair it.
-/

namespace UnsafeHeartbeatLengthTrust

/-- No validation or clamping: the actual payload length is ignored. -/
def unsafe_heartbeat (_payload_len claimed_len : Int) : Int :=
  claimed_len

/-- Boolean counterpart of the five assertions in Python's `check`. -/
def check (candidate : Int → Int → Int) : Bool :=
  (candidate 3 3 == 3) &&
  (candidate 1 65535 == 65535) &&
  (candidate 0 1000 == 1000) &&
  (candidate 100 5 == 5) &&
  (candidate 0 0 == 0)

-- Unit tests: all five source assertions, plus the unrestricted integer domain.
example : unsafe_heartbeat 3 3 = 3 := by native_decide
example : unsafe_heartbeat 1 65535 = 65535 := by native_decide
example : unsafe_heartbeat 0 1000 = 1000 := by native_decide
example : unsafe_heartbeat 100 5 = 5 := by native_decide
example : unsafe_heartbeat 0 0 = 0 := by native_decide
example : unsafe_heartbeat (-3) (-7) = -7 := by native_decide
example : check unsafe_heartbeat = true := by native_decide

#eval unsafe_heartbeat 1 65535
#eval check unsafe_heartbeat

/-- The Python implementation has no input checks or restrictions. -/
def Pre (_payload_len _claimed_len : Int) : Prop := True

/-- The returned length is exactly the untrusted claimed length. -/
def claimed_length_prop (payload_len claimed_len : Int) : Prop :=
  unsafe_heartbeat payload_len claimed_len = claimed_len

theorem claimed_length_thm (payload_len claimed_len : Int) :
    claimed_length_prop payload_len claimed_len := by
  rfl

/-- Changing only the actual payload length cannot change the response length. -/
def payload_independent_prop (payload_len claimed_len : Int) : Prop :=
  ∀ other_payload_len : Int,
    unsafe_heartbeat payload_len claimed_len =
      unsafe_heartbeat other_payload_len claimed_len

theorem payload_independent_thm (payload_len claimed_len : Int) :
    payload_independent_prop payload_len claimed_len := by
  intro other_payload_len
  rfl

/-- An honest claim returns the actual length. -/
def matching_length_prop (payload_len claimed_len : Int) : Prop :=
  claimed_len = payload_len →
    unsafe_heartbeat payload_len claimed_len = payload_len

theorem matching_length_thm (payload_len claimed_len : Int) :
    matching_length_prop payload_len claimed_len := by
  intro h
  exact h

/-- An excessive claim is returned unchanged, with precisely the claimed excess. -/
def overread_prop (payload_len claimed_len : Int) : Prop :=
  payload_len < claimed_len →
    payload_len < unsafe_heartbeat payload_len claimed_len ∧
    unsafe_heartbeat payload_len claimed_len - payload_len = claimed_len - payload_len

theorem overread_thm (payload_len claimed_len : Int) :
    overread_prop payload_len claimed_len := by
  intro h
  exact ⟨h, rfl⟩

/-- The concrete Heartbleed example exposes an excess of 65534 bytes. -/
theorem heartbleed_overread_thm :
    unsafe_heartbeat 1 65535 - 1 = 65534 := by
  norm_num [unsafe_heartbeat]

/-- A smaller claim also determines the result, with precisely that shortfall. -/
def underread_prop (payload_len claimed_len : Int) : Prop :=
  claimed_len < payload_len →
    unsafe_heartbeat payload_len claimed_len < payload_len ∧
    payload_len - unsafe_heartbeat payload_len claimed_len = payload_len - claimed_len

theorem underread_thm (payload_len claimed_len : Int) :
    underread_prop payload_len claimed_len := by
  intro h
  exact ⟨h, rfl⟩

/-- The upper payload bound holds exactly when the untrusted claim already satisfies it. -/
def payload_bound_iff_prop (payload_len claimed_len : Int) : Prop :=
  unsafe_heartbeat payload_len claimed_len ≤ payload_len ↔ claimed_len ≤ payload_len

theorem payload_bound_iff_thm (payload_len claimed_len : Int) :
    payload_bound_iff_prop payload_len claimed_len := by
  exact Iff.rfl

/-- Complete behavioral specification; it deliberately does not promise memory safety. -/
def Post_prop (payload_len claimed_len : Int) : Prop :=
  claimed_length_prop payload_len claimed_len ∧
  payload_independent_prop payload_len claimed_len ∧
  matching_length_prop payload_len claimed_len ∧
  overread_prop payload_len claimed_len ∧
  underread_prop payload_len claimed_len ∧
  payload_bound_iff_prop payload_len claimed_len

/-! ## Property-based tests

Exhaustive bounded checks include every integer from -20 through 20, together
with signed large boundary examples and the source test inputs. Each executable
property has its own check. The independence property's quantified third input
is sampled exhaustively as well. These tests are evidence only; none is used in
any theorem proof.
-/

def testInputs : List Int :=
  (List.range 41).map (fun n => (n : Int) - 20) ++
    [-65535, -1000, -100, 100, 1000, 65535]

-- PBT: claimed_length_prop.
example : testInputs.all (fun p => testInputs.all (fun c =>
    decide (unsafe_heartbeat p c = c))) = true := by
  native_decide

-- PBT: payload_independent_prop, checking every bounded triple.
example : testInputs.all (fun p => testInputs.all (fun c =>
    testInputs.all (fun other =>
      decide (unsafe_heartbeat p c = unsafe_heartbeat other c)))) = true := by
  native_decide

-- PBT: matching_length_prop, including every diagonal (nonvacuous) case.
example : testInputs.all (fun p => testInputs.all (fun c =>
    decide (c = p → unsafe_heartbeat p c = p))) = true := by
  native_decide

-- PBT: overread_prop, including the one-byte / 65535-byte attack.
example : testInputs.all (fun p => testInputs.all (fun c =>
    decide (p < c → p < unsafe_heartbeat p c ∧
      unsafe_heartbeat p c - p = c - p))) = true := by
  native_decide

-- PBT: underread_prop.
example : testInputs.all (fun p => testInputs.all (fun c =>
    decide (c < p → unsafe_heartbeat p c < p ∧
      p - unsafe_heartbeat p c = p - c))) = true := by
  native_decide

-- PBT: payload_bound_iff_prop.
example : testInputs.all (fun p => testInputs.all (fun c =>
    decide (unsafe_heartbeat p c ≤ p ↔ c ≤ p))) = true := by
  native_decide

-- PBT: Post_prop's executable conjunction. The universally quantified
-- independence conjunct is checked over testInputs, not assumed decidable
-- over all Int. Pre is True, so every sampled input is admissible.
example : testInputs.all (fun p => testInputs.all (fun c =>
    decide (unsafe_heartbeat p c = c) &&
    testInputs.all (fun other =>
      decide (unsafe_heartbeat p c = unsafe_heartbeat other c)) &&
    decide (c = p → unsafe_heartbeat p c = p) &&
    decide (p < c → p < unsafe_heartbeat p c ∧
      unsafe_heartbeat p c - p = c - p) &&
    decide (c < p → unsafe_heartbeat p c < p ∧
      p - unsafe_heartbeat p c = p - c) &&
    decide (unsafe_heartbeat p c ≤ p ↔ c ≤ p))) = true := by
  native_decide

/-- Correctness means faithful reproduction of the unsafe source behavior. -/
theorem unsafe_heartbeat_correct (payload_len claimed_len : Int) :
    Pre payload_len claimed_len → Post_prop payload_len claimed_len := by
  intro _
  exact ⟨claimed_length_thm payload_len claimed_len,
    payload_independent_thm payload_len claimed_len,
    matching_length_thm payload_len claimed_len,
    overread_thm payload_len claimed_len,
    underread_thm payload_len claimed_len,
    payload_bound_iff_thm payload_len claimed_len⟩

/-- Mutable response-length state, still without any payload bounds check. -/
def unsafe_heartbeat_imp (_payload_len claimed_len : Int) : Int := Id.run do
  let mut response_len : Int := 0
  response_len := claimed_len
  return response_len

-- Imperative tests repeat the complete source suite.
example : unsafe_heartbeat_imp 3 3 = 3 := by native_decide
example : unsafe_heartbeat_imp 1 65535 = 65535 := by native_decide
example : unsafe_heartbeat_imp 0 1000 = 1000 := by native_decide
example : unsafe_heartbeat_imp 100 5 = 5 := by native_decide
example : unsafe_heartbeat_imp 0 0 = 0 := by native_decide
example : unsafe_heartbeat_imp (-3) (-7) = -7 := by native_decide
example : check unsafe_heartbeat_imp = true := by native_decide

#eval unsafe_heartbeat_imp 1 65535
#eval check unsafe_heartbeat_imp

-- Additional bounded check of the functional/imperative correspondence.
example : testInputs.all (fun p => testInputs.all (fun c =>
    decide (unsafe_heartbeat p c = unsafe_heartbeat_imp p c))) = true := by
  native_decide

/-- The mutable implementation agrees on every Python integer input. -/
theorem functional_imperative_equiv (payload_len claimed_len : Int) :
    unsafe_heartbeat payload_len claimed_len =
      unsafe_heartbeat_imp payload_len claimed_len := by
  rfl

end UnsafeHeartbeatLengthTrust
end Agent
