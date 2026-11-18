import Mathlib
namespace Agent

/-!
# Safe TLS replay check

Translation of the Python `safe_replay_check` and its public test suite.
Python integers are modeled by `Int`, including negative values and with no
machine-word overflow. A message is accepted exactly when its sequence number
is strictly greater than the last-seen sequence number. There is no bound on
the size of an accepted jump.

The function itself is stateless: updating the stored counter is the caller's
responsibility. The replay-after-update property describes a subsequent call
when the caller has stored the accepted message's sequence number. It does not
claim that this predicate alone performs message processing or updates storage.

All named theorems have kernel-checked proofs. `native_decide` is used only for
executable tests. Property-based tests exhaustively cover a small signed domain.
-/

namespace UnsafeReplayAttackSafe

/-- Accept precisely a strictly newer sequence number. -/
def safe_replay_check (message_seq last_seen_seq : Int) : Bool :=
  decide (message_seq > last_seen_seq)

/-- Boolean version of the eight assertions in the Python `check` harness. -/
def check (candidate : Int → Int → Bool) : Bool :=
  candidate 5 4 &&
  !(candidate 3 5) &&
  !(candidate 5 5) &&
  candidate 10 9 &&
  !(candidate 9 10) &&
  candidate 1 0 &&
  !(candidate 0 0) &&
  candidate 100 1

-- Unit tests: every assertion from the source program.
example : safe_replay_check 5 4 = true := by native_decide
example : safe_replay_check 3 5 = false := by native_decide
example : safe_replay_check 5 5 = false := by native_decide
example : safe_replay_check 10 9 = true := by native_decide
example : safe_replay_check 9 10 = false := by native_decide
example : safe_replay_check 1 0 = true := by native_decide
example : safe_replay_check 0 0 = false := by native_decide
example : safe_replay_check 100 1 = true := by native_decide
example : check safe_replay_check = true := by native_decide

-- Additional coverage of Python's signed, arbitrary-precision integer domain.
example : safe_replay_check (-1) (-2) = true := by native_decide
example : safe_replay_check (-2) (-1) = false := by native_decide
example : safe_replay_check (-5) (-5) = false := by native_decide
example : safe_replay_check 1000000000000000000000000000000 1 = true := by
  native_decide

#eval safe_replay_check 5 4
#eval safe_replay_check 3 5
#eval check safe_replay_check

/-- All integer inputs are admissible; the Python code imposes no restriction. -/
def Pre (_message_seq _last_seen_seq : Int) : Prop := True

/-- Exact acceptance characterization, in both directions. -/
def acceptance_prop (message_seq last_seen_seq : Int) : Prop :=
  safe_replay_check message_seq last_seen_seq = true ↔ last_seen_seq < message_seq

theorem acceptance_thm (message_seq last_seen_seq : Int) :
    acceptance_prop message_seq last_seen_seq := by
  simp [acceptance_prop, safe_replay_check]

/-- Exact rejection characterization, including equality. -/
def rejection_prop (message_seq last_seen_seq : Int) : Prop :=
  safe_replay_check message_seq last_seen_seq = false ↔ message_seq ≤ last_seen_seq

theorem rejection_thm (message_seq last_seen_seq : Int) :
    rejection_prop message_seq last_seen_seq := by
  simp [rejection_prop, safe_replay_check, not_lt]

/-- Every strictly newer sequence is accepted, regardless of the gap. -/
def fresh_message_prop (message_seq last_seen_seq : Int) : Prop :=
  last_seen_seq < message_seq → safe_replay_check message_seq last_seen_seq = true

theorem fresh_message_thm (message_seq last_seen_seq : Int) :
    fresh_message_prop message_seq last_seen_seq := by
  exact (acceptance_thm message_seq last_seen_seq).mpr

/-- An older or already-seen sequence is rejected. -/
def replay_rejection_prop (message_seq last_seen_seq : Int) : Prop :=
  message_seq ≤ last_seen_seq → safe_replay_check message_seq last_seen_seq = false

theorem replay_rejection_thm (message_seq last_seen_seq : Int) :
    replay_rejection_prop message_seq last_seen_seq := by
  exact (rejection_thm message_seq last_seen_seq).mpr

/-- In particular, an equal sequence number is always a duplicate. -/
def duplicate_rejection_prop (last_seen_seq : Int) : Prop :=
  safe_replay_check last_seen_seq last_seen_seq = false

theorem duplicate_rejection_thm (last_seen_seq : Int) :
    duplicate_rejection_prop last_seen_seq := by
  simp [duplicate_rejection_prop, safe_replay_check]

/-- Acceptance guarantees strict progression of the sequence counter. -/
def monotonic_progression_prop (message_seq last_seen_seq : Int) : Prop :=
  safe_replay_check message_seq last_seen_seq = true → last_seen_seq < message_seq

theorem monotonic_progression_thm (message_seq last_seen_seq : Int) :
    monotonic_progression_prop message_seq last_seen_seq := by
  exact (acceptance_thm message_seq last_seen_seq).mp

/-- After storing an accepted sequence, it and all earlier sequences are blocked. -/
def replay_after_update_prop (message_seq last_seen_seq replay_seq : Int) : Prop :=
  safe_replay_check message_seq last_seen_seq = true →
  replay_seq ≤ message_seq → safe_replay_check replay_seq message_seq = false

theorem replay_after_update_thm (message_seq last_seen_seq replay_seq : Int) :
    replay_after_update_prop message_seq last_seen_seq replay_seq := by
  intro _accepted hReplay
  exact replay_rejection_thm replay_seq message_seq hReplay

/-- Complete contract, including the caller-updated-counter consequence. -/
def Post_prop (message_seq last_seen_seq : Int) : Prop :=
  acceptance_prop message_seq last_seen_seq ∧
  rejection_prop message_seq last_seen_seq ∧
  fresh_message_prop message_seq last_seen_seq ∧
  replay_rejection_prop message_seq last_seen_seq ∧
  duplicate_rejection_prop last_seen_seq ∧
  monotonic_progression_prop message_seq last_seen_seq ∧
  (∀ replay_seq : Int, replay_after_update_prop message_seq last_seen_seq replay_seq)

/-! ## Property-based tests

These are exhaustive bounded PBTs, not just the source's fixed examples.
`pbtSeqs` contains every integer from -15 through 15. Pair tests cover 961
inputs, and replay-after-update tests cover 29,791 triples. Each test spells out
the executable Boolean form of its named property; no decidability instance
for the universally quantified post-condition is needed. `Pre` is always true.
-/

private def pbtSeqs : List Int :=
  (List.range 31).map (fun n => (n : Int) - 15)

-- PBT for acceptance_prop.
example : (pbtSeqs.all fun m => pbtSeqs.all fun l =>
    safe_replay_check m l == decide (l < m)) = true := by
  native_decide

-- PBT for rejection_prop.
example : (pbtSeqs.all fun m => pbtSeqs.all fun l =>
    (!(safe_replay_check m l)) == decide (m ≤ l)) = true := by
  native_decide

-- PBT for fresh_message_prop: executable implication.
example : (pbtSeqs.all fun m => pbtSeqs.all fun l =>
    !(decide (l < m)) || safe_replay_check m l) = true := by
  native_decide

-- PBT for replay_rejection_prop.
example : (pbtSeqs.all fun m => pbtSeqs.all fun l =>
    !(decide (m ≤ l)) || !(safe_replay_check m l)) = true := by
  native_decide

-- PBT for duplicate_rejection_prop.
example : (pbtSeqs.all fun l => !(safe_replay_check l l)) = true := by
  native_decide

-- PBT for monotonic_progression_prop.
example : (pbtSeqs.all fun m => pbtSeqs.all fun l =>
    !(safe_replay_check m l) || decide (l < m)) = true := by
  native_decide

-- PBT for replay_after_update_prop.
example : (pbtSeqs.all fun m => pbtSeqs.all fun l => pbtSeqs.all fun r =>
    !(safe_replay_check m l) || !(decide (r ≤ m)) ||
      !(safe_replay_check r m)) = true := by
  native_decide

-- PBT for Post_prop: every conjunct, with the final universal bounded over pbtSeqs.
example : (pbtSeqs.all fun m => pbtSeqs.all fun l =>
    (safe_replay_check m l == decide (l < m)) &&
    ((!(safe_replay_check m l)) == decide (m ≤ l)) &&
    (!(decide (l < m)) || safe_replay_check m l) &&
    (!(decide (m ≤ l)) || !(safe_replay_check m l)) &&
    (!(safe_replay_check l l)) &&
    (!(safe_replay_check m l) || decide (l < m)) &&
    (pbtSeqs.all fun r => !(safe_replay_check m l) ||
      !(decide (r ≤ m)) || !(safe_replay_check r m))) = true := by
  native_decide

/-- The functional implementation meets the entire contract on all valid inputs. -/
theorem safe_replay_check_correct (message_seq last_seen_seq : Int) :
    Pre message_seq last_seen_seq → Post_prop message_seq last_seen_seq := by
  intro _hPre
  exact ⟨acceptance_thm message_seq last_seen_seq,
    rejection_thm message_seq last_seen_seq,
    fresh_message_thm message_seq last_seen_seq,
    replay_rejection_thm message_seq last_seen_seq,
    duplicate_rejection_thm last_seen_seq,
    monotonic_progression_thm message_seq last_seen_seq,
    fun replay_seq => replay_after_update_thm message_seq last_seen_seq replay_seq⟩

/-- Imperative formulation with a mutable acceptance flag. -/
def safe_replay_check_imperative (message_seq last_seen_seq : Int) : Bool := Id.run do
  let mut accepted := false
  if message_seq > last_seen_seq then
    accepted := true
  return accepted

-- Imperative unit tests reproduce all eight source assertions.
example : safe_replay_check_imperative 5 4 = true := by native_decide
example : safe_replay_check_imperative 3 5 = false := by native_decide
example : safe_replay_check_imperative 5 5 = false := by native_decide
example : safe_replay_check_imperative 10 9 = true := by native_decide
example : safe_replay_check_imperative 9 10 = false := by native_decide
example : safe_replay_check_imperative 1 0 = true := by native_decide
example : safe_replay_check_imperative 0 0 = false := by native_decide
example : safe_replay_check_imperative 100 1 = true := by native_decide
example : check safe_replay_check_imperative = true := by native_decide
#eval check safe_replay_check_imperative

-- Bounded cross-implementation test, supplementary to the proof below.
example : (pbtSeqs.all fun m => pbtSeqs.all fun l =>
    safe_replay_check m l == safe_replay_check_imperative m l) = true := by
  native_decide

/-- Functional and mutable-state formulations coincide for every pair of integers. -/
theorem functional_imperative_equivalence (message_seq last_seen_seq : Int) :
    safe_replay_check message_seq last_seen_seq =
      safe_replay_check_imperative message_seq last_seen_seq := by
  by_cases h : message_seq > last_seen_seq <;>
    simp [safe_replay_check, safe_replay_check_imperative, h]

end UnsafeReplayAttackSafe
end Agent
