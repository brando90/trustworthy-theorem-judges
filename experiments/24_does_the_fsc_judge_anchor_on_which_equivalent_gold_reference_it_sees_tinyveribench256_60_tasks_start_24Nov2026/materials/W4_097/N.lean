import Mathlib
namespace Agent

/-!
# Handshake payload with identity binding

A translation of the Python integer functions `safe_handshake_msg`, `safe_accept`,
and the seven assertions in `check`. Python's arbitrary-precision signed integers
are modelled by `Int`; there are no range restrictions on keys or identities.
`check` is the Boolean conjunction of the Python assertions (rather than an
exception-raising procedure).

Acceptance compares the entire computed payload. Changing just the key, sender,
or recipient changes that payload, as does swapping distinct identities. This
linear encoding is NOT injective on arbitrary integer triples: simultaneous
changes to different coordinates can cancel. We therefore do not claim that
acceptance implies equality of all three coordinates.
-/

namespace SafeHandshakeNoIdBindingSafe

/-! ## Functional implementation -/

def safe_handshake_msg (session_key alice bob : Int) : Int :=
  session_key + 100 * alice + 10000 * bob

def safe_accept (msg expected_key expected_alice expected_bob : Int) : Bool :=
  decide (msg = safe_handshake_msg expected_key expected_alice expected_bob)

def check (candidate : Int → Int → Int → Int) : Bool :=
  let msg := candidate 42 1 2
  safe_accept msg 42 1 2 &&
    !(safe_accept msg 42 1 99) &&
    !(safe_accept msg 42 7 2) &&
    !(safe_accept msg 99 1 2) &&
    decide (candidate 42 1 2 ≠ candidate 42 1 3) &&
    decide (candidate 7 1 2 ≠ candidate 7 2 1) &&
    decide (candidate 0 0 0 = 0)

/-! ## Unit tests: the seven Python assertions -/

example : safe_accept (safe_handshake_msg 42 1 2) 42 1 2 = true := by native_decide
example : safe_accept (safe_handshake_msg 42 1 2) 42 1 99 = false := by native_decide
example : safe_accept (safe_handshake_msg 42 1 2) 42 7 2 = false := by native_decide
example : safe_accept (safe_handshake_msg 42 1 2) 99 1 2 = false := by native_decide
example : safe_handshake_msg 42 1 2 ≠ safe_handshake_msg 42 1 3 := by native_decide
example : safe_handshake_msg 7 1 2 ≠ safe_handshake_msg 7 2 1 := by native_decide
example : safe_handshake_msg 0 0 0 = 0 := by native_decide
example : check safe_handshake_msg = true := by native_decide
example : safe_handshake_msg (-42) (-1) (-2) = -20142 := by native_decide
-- A deliberate collision illustrates why no global triple-injectivity is claimed.
example : safe_accept (safe_handshake_msg 100 0 0) 0 1 0 = true := by native_decide

#eval safe_handshake_msg 42 1 2
#eval safe_accept (safe_handshake_msg 42 1 2) 42 1 99
#eval check safe_handshake_msg

/-! ## Preconditions and universally quantified properties -/

/-- Every Python integer triple is admissible. -/
def Pre (_session_key _alice _bob : Int) : Prop := True

/-- The exact arithmetic encoding, without modular arithmetic or overflow. -/
def encoding_prop (k a b : Int) : Prop :=
  safe_handshake_msg k a b = k + 100 * a + 10000 * b

theorem encoding_thm (k a b : Int) : encoding_prop k a b := by sorry

/-- Acceptance is exactly equality with the expected encoded payload. -/
def accept_exact_prop (msg k a b : Int) : Prop :=
  safe_accept msg k a b = true ↔ msg = safe_handshake_msg k a b

theorem accept_exact_thm (msg k a b : Int) : accept_exact_prop msg k a b := by sorry

/-- The matching triple is always accepted. -/
def matching_prop (k a b : Int) : Prop :=
  safe_accept (safe_handshake_msg k a b) k a b = true

theorem matching_thm (k a b : Int) : matching_prop k a b := by sorry

/-- With the other coordinates fixed, a different recipient is rejected. -/
def recipient_reject_prop (k a b other_b : Int) : Prop :=
  other_b ≠ b → safe_accept (safe_handshake_msg k a b) k a other_b = false

theorem recipient_reject_thm (k a b other_b : Int) :
    recipient_reject_prop k a b other_b := by sorry

/-- With the other coordinates fixed, a different sender is rejected. -/
def sender_reject_prop (k a b other_a : Int) : Prop :=
  other_a ≠ a → safe_accept (safe_handshake_msg k a b) k other_a b = false

theorem sender_reject_thm (k a b other_a : Int) :
    sender_reject_prop k a b other_a := by sorry

/-- With the identities fixed, a different key is rejected. -/
def key_reject_prop (k a b other_k : Int) : Prop :=
  other_k ≠ k → safe_accept (safe_handshake_msg k a b) other_k a b = false

theorem key_reject_thm (k a b other_k : Int) :
    key_reject_prop k a b other_k := by sorry

/-- Distinct recipients produce distinct payloads for a fixed key and sender. -/
def recipient_distinct_prop (k a b other_b : Int) : Prop :=
  b ≠ other_b → safe_handshake_msg k a b ≠ safe_handshake_msg k a other_b

theorem recipient_distinct_thm (k a b other_b : Int) :
    recipient_distinct_prop k a b other_b := by sorry

/-- Swapping different identities changes the payload. Equal identities need not. -/
def swapping_prop (k a b : Int) : Prop :=
  a ≠ b → safe_handshake_msg k a b ≠ safe_handshake_msg k b a

theorem swapping_thm (k a b : Int) : swapping_prop k a b := by sorry

/-- Generalization of the all-zero edge case to every key. -/
def zero_identities_prop (k : Int) : Prop :=
  safe_handshake_msg k 0 0 = k

theorem zero_identities_thm (k : Int) : zero_identities_prop k := by sorry

/-- The complete public Python check, proved by kernel computation. -/
theorem check_thm : check safe_handshake_msg = true := by sorry

/-! ## Postcondition -/

def Post_prop (k a b : Int) : Prop :=
  encoding_prop k a b ∧
  (∀ msg : Int, accept_exact_prop msg k a b) ∧
  matching_prop k a b ∧
  (∀ other_b : Int, recipient_reject_prop k a b other_b) ∧
  (∀ other_a : Int, sender_reject_prop k a b other_a) ∧
  (∀ other_k : Int, key_reject_prop k a b other_k) ∧
  (∀ other_b : Int, recipient_distinct_prop k a b other_b) ∧
  swapping_prop k a b ∧
  zero_identities_prop k

/-! ## Property-based tests

These are exhaustive bounded tests, not proofs of the universal specifications.
The sampled integers include negatives and zero. Each implication is executable
and includes both equal and distinct alternatives; no rejection test relies on
an empty admissible sample. The postcondition's unbounded quantifiers are tested
on the same finite domain (and on the actual payload for message comparisons).
-/

private def sampleInts : List Int :=
  (List.range 9).map (fun n => (n : Int) - 4)

private def allTriples (test : Int → Int → Int → Bool) : Bool :=
  sampleInts.all fun k => sampleInts.all fun a => sampleInts.all fun b => test k a b

-- PBT for encoding_prop.
example : allTriples (fun k a b =>
    decide (safe_handshake_msg k a b = k + 100 * a + 10000 * b)) = true := by
  native_decide

-- PBT for accept_exact_prop, including both matching and arbitrary messages.
example : allTriples (fun k a b =>
    (safe_handshake_msg k a b :: sampleInts).all fun msg =>
      decide ((safe_accept msg k a b = true) ↔ msg = safe_handshake_msg k a b))
    = true := by native_decide

-- PBT for matching_prop.
example : allTriples (fun k a b => safe_accept (safe_handshake_msg k a b) k a b)
    = true := by native_decide

-- PBT for recipient_reject_prop.
example : allTriples (fun k a b => sampleInts.all fun other_b =>
    decide (other_b ≠ b → safe_accept (safe_handshake_msg k a b) k a other_b = false))
    = true := by native_decide

-- PBT for sender_reject_prop.
example : allTriples (fun k a b => sampleInts.all fun other_a =>
    decide (other_a ≠ a → safe_accept (safe_handshake_msg k a b) k other_a b = false))
    = true := by native_decide

-- PBT for key_reject_prop.
example : allTriples (fun k a b => sampleInts.all fun other_k =>
    decide (other_k ≠ k → safe_accept (safe_handshake_msg k a b) other_k a b = false))
    = true := by native_decide

-- PBT for recipient_distinct_prop.
example : allTriples (fun k a b => sampleInts.all fun other_b =>
    decide (b ≠ other_b → safe_handshake_msg k a b ≠ safe_handshake_msg k a other_b))
    = true := by native_decide

-- PBT for swapping_prop.
example : allTriples (fun k a b =>
    decide (a ≠ b → safe_handshake_msg k a b ≠ safe_handshake_msg k b a))
    = true := by native_decide

-- PBT for zero_identities_prop, including the original k = 0 edge case.
example : sampleInts.all (fun k => decide (safe_handshake_msg k 0 0 = k))
    = true := by native_decide

/-- Executable bounded specialization of every conjunct of Post_prop. -/
private def postCheck (k a b : Int) : Bool :=
  decide (safe_handshake_msg k a b = k + 100 * a + 10000 * b) &&
  ((safe_handshake_msg k a b :: sampleInts).all fun msg =>
    decide ((safe_accept msg k a b = true) ↔ msg = safe_handshake_msg k a b)) &&
  safe_accept (safe_handshake_msg k a b) k a b &&
  (sampleInts.all fun other_b =>
    decide (other_b ≠ b → safe_accept (safe_handshake_msg k a b) k a other_b = false)) &&
  (sampleInts.all fun other_a =>
    decide (other_a ≠ a → safe_accept (safe_handshake_msg k a b) k other_a b = false)) &&
  (sampleInts.all fun other_k =>
    decide (other_k ≠ k → safe_accept (safe_handshake_msg k a b) other_k a b = false)) &&
  (sampleInts.all fun other_b =>
    decide (b ≠ other_b → safe_handshake_msg k a b ≠ safe_handshake_msg k a other_b)) &&
  decide (a ≠ b → safe_handshake_msg k a b ≠ safe_handshake_msg k b a) &&
  decide (safe_handshake_msg k 0 0 = k)

-- PBT for Post_prop: all 729 sampled triples and all sampled alternatives.
example : allTriples postCheck = true := by native_decide
#eval allTriples postCheck

/-! ## Correctness -/

theorem correctness_thm (k a b : Int) : Pre k a b → Post_prop k a b := by sorry

/-! ## Imperative implementations with mutable state -/

def safe_handshake_msg_imp (session_key alice bob : Int) : Int := Id.run do
  let mut payload := session_key
  payload := payload + 100 * alice
  payload := payload + 10000 * bob
  return payload

def safe_accept_imp (msg expected_key expected_alice expected_bob : Int) : Bool := Id.run do
  let mut expected := expected_key
  expected := expected + 100 * expected_alice
  expected := expected + 10000 * expected_bob
  let mut accepted := false
  if msg = expected then
    accepted := true
  return accepted

def check_imp (candidate : Int → Int → Int → Int) : Bool := Id.run do
  let msg := candidate 42 1 2
  let mut passed := true
  passed := passed && safe_accept_imp msg 42 1 2
  passed := passed && !(safe_accept_imp msg 42 1 99)
  passed := passed && !(safe_accept_imp msg 42 7 2)
  passed := passed && !(safe_accept_imp msg 99 1 2)
  passed := passed && decide (candidate 42 1 2 ≠ candidate 42 1 3)
  passed := passed && decide (candidate 7 1 2 ≠ candidate 7 2 1)
  passed := passed && decide (candidate 0 0 0 = 0)
  return passed

/-! ## Imperative tests -/

example : safe_accept_imp (safe_handshake_msg_imp 42 1 2) 42 1 2 = true := by native_decide
example : safe_accept_imp (safe_handshake_msg_imp 42 1 2) 42 1 99 = false := by native_decide
example : safe_accept_imp (safe_handshake_msg_imp 42 1 2) 42 7 2 = false := by native_decide
example : safe_accept_imp (safe_handshake_msg_imp 42 1 2) 99 1 2 = false := by native_decide
example : safe_handshake_msg_imp 42 1 2 ≠ safe_handshake_msg_imp 42 1 3 := by native_decide
example : safe_handshake_msg_imp 7 1 2 ≠ safe_handshake_msg_imp 7 2 1 := by native_decide
example : safe_handshake_msg_imp 0 0 0 = 0 := by native_decide
example : check_imp safe_handshake_msg_imp = true := by native_decide
example : allTriples (fun k a b =>
    decide (safe_handshake_msg k a b = safe_handshake_msg_imp k a b)) = true := by
  native_decide

-- Bounded verifier-equivalence test, with accepted and rejected messages.
example : allTriples (fun k a b =>
    (safe_handshake_msg k a b :: sampleInts).all fun msg =>
      decide (safe_accept msg k a b = safe_accept_imp msg k a b)) = true := by
  native_decide

-- Exercise check equivalence on a family containing good and bad candidates.
example : sampleInts.all (fun offset =>
    let candidate := fun k a b => safe_handshake_msg k a b + offset
    decide (check candidate = check_imp candidate)) = true := by native_decide

#eval safe_handshake_msg_imp 42 1 2
#eval check_imp safe_handshake_msg_imp

/-! ## Functional/imperative equivalence -/

theorem handshake_equiv_thm (k a b : Int) :
    safe_handshake_msg k a b = safe_handshake_msg_imp k a b := by sorry

theorem accept_equiv_thm (msg k a b : Int) :
    safe_accept msg k a b = safe_accept_imp msg k a b := by sorry

theorem check_equiv_thm (candidate : Int → Int → Int → Int) :
    check candidate = check_imp candidate := by sorry

theorem complete_check_equiv_thm :
    check safe_handshake_msg = check_imp safe_handshake_msg_imp := by sorry

end SafeHandshakeNoIdBindingSafe
end Agent
