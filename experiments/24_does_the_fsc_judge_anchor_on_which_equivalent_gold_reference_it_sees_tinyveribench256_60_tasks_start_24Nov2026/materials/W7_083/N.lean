import Mathlib
namespace Agent

/-!
# Unsafe TLS replay checking

This file translates the Python `unsafe_replay_check` function and its test
harness. Python integers are modeled by `Int`, with no sign or size restriction.
The function deliberately accepts every message: neither the message identifier
nor the last seen sequence number is inspected. In particular, old messages and
duplicate messages are accepted, and repeated delivery is not prevented.

The specifications describe this vulnerability; they do not repair it or claim
that the implementation provides replay protection. Bounded executable tests are
separate from the universally quantified, kernel-checked proofs.
-/

namespace UnsafeReplayAttack

/-! ## Functional implementation -/

/-- Always accept, exactly as in the Python implementation. -/
def unsafe_replay_check (_message_id _last_seen_seq : Int) : Bool :=
  true

/-- Boolean form of the six assertions in the Python `check` harness. -/
def check (candidate : Int → Int → Bool) : Bool :=
  candidate 5 4 &&
  candidate 3 5 &&
  candidate 5 5 &&
  candidate 1 100 &&
  candidate 100 1 &&
  candidate 0 0

/-! ## Unit tests -/

example : unsafe_replay_check 5 4 = true := by native_decide
example : unsafe_replay_check 3 5 = true := by native_decide
example : unsafe_replay_check 5 5 = true := by native_decide
example : unsafe_replay_check 1 100 = true := by native_decide
example : unsafe_replay_check 100 1 = true := by native_decide
example : unsafe_replay_check 0 0 = true := by native_decide
example : unsafe_replay_check (-3) (-1) = true := by native_decide
example : unsafe_replay_check 0 (-100) = true := by native_decide
example : check unsafe_replay_check = true := by native_decide

#eval unsafe_replay_check 3 5
#eval check unsafe_replay_check
#eval if check unsafe_replay_check then "All tests passed." else "Candidate failed tests"

/-! ## Precondition -/

/-- Every pair of Python integers is admissible. -/
def Pre (_message_id _last_seen_seq : Int) : Prop := True

/-! ## Properties and kernel-checked proofs -/

/-- Acceptance is unconditional, not just restricted to the unit-test inputs. -/
def always_accepts_prop (message_id last_seen_seq : Int) : Prop :=
  unsafe_replay_check message_id last_seen_seq = true

theorem always_accepts_thm (message_id last_seen_seq : Int) :
    always_accepts_prop message_id last_seen_seq := by sorry

/-- A genuinely newer message is accepted. -/
def new_message_prop (message_id last_seen_seq : Int) : Prop :=
  last_seen_seq < message_id →
    unsafe_replay_check message_id last_seen_seq = true

theorem new_message_thm (message_id last_seen_seq : Int) :
    new_message_prop message_id last_seen_seq := by sorry

/-- Vulnerability: a message older than the last seen sequence is also accepted. -/
def replay_accepted_prop (message_id last_seen_seq : Int) : Prop :=
  message_id < last_seen_seq →
    unsafe_replay_check message_id last_seen_seq = true

theorem replay_accepted_thm (message_id last_seen_seq : Int) :
    replay_accepted_prop message_id last_seen_seq := by sorry

/-- Vulnerability: a duplicate of the last seen sequence is accepted. -/
def duplicate_accepted_prop (message_id last_seen_seq : Int) : Prop :=
  message_id = last_seen_seq →
    unsafe_replay_check message_id last_seen_seq = true

theorem duplicate_accepted_thm (message_id last_seen_seq : Int) :
    duplicate_accepted_prop message_id last_seen_seq := by sorry

/-- Changing either or both arguments has no effect on the result. -/
def inputs_ignored_prop (message_id last_seen_seq : Int) : Prop :=
  ∀ other_message other_last : Int,
    unsafe_replay_check message_id last_seen_seq =
      unsafe_replay_check other_message other_last

theorem inputs_ignored_thm (message_id last_seen_seq : Int) :
    inputs_ignored_prop message_id last_seen_seq := by sorry

/-- Any number of repeated deliveries produces that many acceptances.
This models repeated calls, not an additional TLS processing implementation. -/
def repeated_replay_prop (message_id last_seen_seq : Int) (count : Nat) : Prop :=
  (List.replicate count message_id).map
      (fun message => unsafe_replay_check message last_seen_seq) =
    List.replicate count true

theorem repeated_replay_thm (message_id last_seen_seq : Int) (count : Nat) :
    repeated_replay_prop message_id last_seen_seq count := by sorry

/-! ## Postcondition -/

/-- All behavior claims, including independence of all alternative inputs and
acceptance of arbitrarily many repeats, hold simultaneously. -/
def Post_prop (message_id last_seen_seq : Int) : Prop :=
  always_accepts_prop message_id last_seen_seq ∧
  new_message_prop message_id last_seen_seq ∧
  replay_accepted_prop message_id last_seen_seq ∧
  duplicate_accepted_prop message_id last_seen_seq ∧
  inputs_ignored_prop message_id last_seen_seq ∧
  (∀ count : Nat, repeated_replay_prop message_id last_seen_seq count)

/-! ## Property-based tests

Exhaustively test every pair of integers from -10 through 10. Independence also
ranges over every alternative pair in that interval, and repeated delivery
ranges over counts 0 through 20. Each test below checks an executable Boolean
form of the named property. Implications are represented by `!premise || result`.
These finite tests do not restrict the domains of any theorem or specification.
-/

private def testIntegers : List Int :=
  (List.range 21).map (fun n => (n : Int) - 10)

private def testPairs (p : Int → Int → Bool) : Bool :=
  testIntegers.all (fun message_id =>
    testIntegers.all (fun last_seen_seq => p message_id last_seen_seq))

private def newMessageTest (message_id last_seen_seq : Int) : Bool :=
  (!decide (last_seen_seq < message_id)) ||
    unsafe_replay_check message_id last_seen_seq

private def replayAcceptedTest (message_id last_seen_seq : Int) : Bool :=
  (!decide (message_id < last_seen_seq)) ||
    unsafe_replay_check message_id last_seen_seq

private def duplicateAcceptedTest (message_id last_seen_seq : Int) : Bool :=
  (!decide (message_id = last_seen_seq)) ||
    unsafe_replay_check message_id last_seen_seq

private def inputsIgnoredTest (message_id last_seen_seq : Int) : Bool :=
  testPairs (fun other_message other_last =>
    unsafe_replay_check message_id last_seen_seq ==
      unsafe_replay_check other_message other_last)

private def repeatedReplayTest (message_id last_seen_seq : Int) : Bool :=
  (List.range 21).all (fun count =>
    ((List.replicate count message_id).map
      (fun message => unsafe_replay_check message last_seen_seq)) ==
        List.replicate count true)

private def postTest (message_id last_seen_seq : Int) : Bool :=
  unsafe_replay_check message_id last_seen_seq &&
  newMessageTest message_id last_seen_seq &&
  replayAcceptedTest message_id last_seen_seq &&
  duplicateAcceptedTest message_id last_seen_seq &&
  inputsIgnoredTest message_id last_seen_seq &&
  repeatedReplayTest message_id last_seen_seq

-- PBT for always_accepts_prop: 441 input pairs, including negative integers.
example : testPairs unsafe_replay_check = true := by native_decide

-- PBT for new_message_prop.
example : testPairs newMessageTest = true := by native_decide

-- PBT for replay_accepted_prop.
example : testPairs replayAcceptedTest = true := by native_decide

-- PBT for duplicate_accepted_prop.
example : testPairs duplicateAcceptedTest = true := by native_decide

-- PBT for inputs_ignored_prop: all 21^4 combinations of the four integers.
example : testPairs inputsIgnoredTest = true := by native_decide

-- PBT for repeated_replay_prop: all 441 pairs and all 21 repetition counts.
example : testPairs repeatedReplayTest = true := by native_decide

-- PBT for the entire Post_prop, using the same finite universal ranges.
example : testPairs postTest = true := by native_decide

#eval ("Bounded postcondition PBT", testPairs postTest)

/-! ## Correctness -/

/-- Correctness means fidelity to the unsafe specification, not TLS security. -/
theorem correctness_thm (message_id last_seen_seq : Int) :
    Pre message_id last_seen_seq → Post_prop message_id last_seen_seq := by sorry

/-! ## Imperative implementation -/

/-- Mutable local acceptance state, still with no sequence tracking or checks. -/
def unsafe_replay_check_imperative (_message_id _last_seen_seq : Int) : Bool := Id.run do
  let mut accepted : Bool := false
  accepted := true
  return accepted

/-! ## Imperative tests -/

example : unsafe_replay_check_imperative 5 4 = true := by native_decide
example : unsafe_replay_check_imperative 3 5 = true := by native_decide
example : unsafe_replay_check_imperative 5 5 = true := by native_decide
example : unsafe_replay_check_imperative 1 100 = true := by native_decide
example : unsafe_replay_check_imperative 100 1 = true := by native_decide
example : unsafe_replay_check_imperative 0 0 = true := by native_decide
example : unsafe_replay_check_imperative (-3) (-1) = true := by native_decide
example : check unsafe_replay_check_imperative = true := by native_decide

#eval check unsafe_replay_check_imperative

example : testPairs (fun message_id last_seen_seq =>
    unsafe_replay_check message_id last_seen_seq ==
      unsafe_replay_check_imperative message_id last_seen_seq) = true := by
  native_decide

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equivalence_thm (message_id last_seen_seq : Int) :
    unsafe_replay_check message_id last_seen_seq =
      unsafe_replay_check_imperative message_id last_seen_seq := by sorry

theorem implementations_equal_thm :
    unsafe_replay_check = unsafe_replay_check_imperative := by sorry

end UnsafeReplayAttack
end Agent
