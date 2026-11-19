/-!
# Unsafe replay check

This file translates a Python teaching model from MIT 6.858 into Lean 4. The
check accepts every message without looking at its sequence number, so it
gives no protection against replayed messages.

Python `int` is unbounded, so both arguments are modelled as `Int`.
-/

namespace UnsafeReplay

/-- Accept a message without checking its sequence number. -/
def unsafeReplayCheck (_messageId : Int) (_lastSeenSeq : Int) : Bool :=
  true  -- Always accept: no replay protection

/-- The fixed examples from the Python `check` function. The result is `true`
exactly when every assertion holds. -/
def check (candidate : Int → Int → Bool) : Bool :=
  candidate 5 4 == true &&
  candidate 3 5 == true &&
  candidate 5 5 == true &&
  candidate 1 100 == true &&
  candidate 0 0 == true

/-- Equivalent of `assert check(unsafe_replay_check)`. -/
theorem check_unsafeReplayCheck : check unsafeReplayCheck = true := by decide

/-! ## Basic behaviour -/

/-- The check accepts every input. -/
theorem unsafeReplayCheck_always_true (m s : Int) :
    unsafeReplayCheck m s = true := rfl

/-- The result does not depend on either argument. -/
theorem unsafeReplayCheck_const (m s m' s' : Int) :
    unsafeReplayCheck m s = unsafeReplayCheck m' s' := rfl

/-- A replayed or stale message (id at most the last seen sequence number)
is still accepted. This is the vulnerability. -/
theorem unsafeReplayCheck_accepts_replay (m s : Int) (_h : m ≤ s) :
    unsafeReplayCheck m s = true := rfl

/-- The same message delivered twice is accepted both times. -/
theorem unsafeReplayCheck_accepts_duplicate (m : Int) :
    unsafeReplayCheck m m = true ∧ unsafeReplayCheck m m = true :=
  ⟨rfl, rfl⟩

/-! ## A replay-safety specification -/

/-- A check is replay-safe if it rejects every message whose id is not
strictly greater than the last seen sequence number. -/
def ReplaySafe (f : Int → Int → Bool) : Prop :=
  ∀ m s : Int, m ≤ s → f m s = false

/-- A reference check that accepts only strictly fresh messages. -/
def safeReplayCheck (messageId lastSeenSeq : Int) : Bool :=
  decide (lastSeenSeq < messageId)

theorem safeReplayCheck_accepts_fresh (m s : Int) (h : s < m) :
    safeReplayCheck m s = true :=
  decide_eq_true h

theorem safeReplayCheck_rejects_replay (m s : Int) (h : m ≤ s) :
    safeReplayCheck m s = false :=
  decide_eq_false (by omega)

theorem safeReplayCheck_replaySafe : ReplaySafe safeReplayCheck :=
  fun m s h => safeReplayCheck_rejects_replay m s h

/-- The unsafe check fails the replay-safety specification. -/
theorem unsafeReplayCheck_not_replaySafe : ¬ ReplaySafe unsafeReplayCheck := by
  intro h
  have := h 0 0 (Int.le_refl 0)
  simp [unsafeReplayCheck] at this

/-- The unsafe check and the safe check are different functions. -/
theorem unsafe_ne_safe : unsafeReplayCheck ≠ safeReplayCheck := by
  intro h
  have := congrFun (congrFun h 5) 5
  exact absurd this (by decide)

/-- The test suite rejects the safe check: its fixed examples require stale
messages such as `(3, 5)` and `(5, 5)` to be accepted. -/
theorem check_rejects_safe : check safeReplayCheck = false := by decide

/-- Any check that passes the test suite accepts the replay `(5, 5)`, so it
cannot be replay-safe. -/
theorem check_implies_not_replaySafe (f : Int → Int → Bool)
    (hc : check f = true) : ¬ ReplaySafe f := by
  intro hs
  have h55 : f 5 5 = false := hs 5 5 (Int.le_refl 5)
  simp [check, h55] at hc

end UnsafeReplay

open UnsafeReplay in
def main : IO Unit := do
  if check unsafeReplayCheck then
    IO.println "All tests passed."
  else
    throw (IO.userError "Candidate failed tests")

/-!
TLDR-end: [lean-translation: unsafe_replay_check] This is a Lean 4 translation
with the test suite proved by `decide`. The theorems show that the check
accepts every message, including replays, and so fails a replay-safety
specification. They also show that any function passing the given tests must
accept the replay `(5, 5)`. I could not compile the file in this session
because no shell was available.
-/
