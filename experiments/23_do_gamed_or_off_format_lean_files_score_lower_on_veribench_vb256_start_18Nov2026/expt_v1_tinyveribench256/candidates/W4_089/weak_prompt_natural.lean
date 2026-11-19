/-!
# Sender-anonymous server log (MIT 6.858 teaching model)

A Lean 4 translation of a small Python program:

* `safe_log` returns a server-log entry with the recipient ID and the timestamp,
  and stores `None` for the sender ID.
* `adversary_read_sender` models an adversary that reads the `sender_id` field.
* `check` runs five fixed examples against a candidate logger.

Modelling choices:
* Python `int` has no size limit, so it becomes `Int`.
* The Python `dict` with the keys `sender_id`, `recipient_id` and `timestamp`
  becomes the structure `LogEntry`, and Python `None` becomes `Option.none`.
  `dict.get` gives `None` both for a missing key and for a stored `None`, so the
  type `Option Int` covers both cases.
* Python's `check` raises `AssertionError` when an observation does not match.
  Here it returns `false` instead.
-/

namespace SafeLog

/-- A server-log entry. `senderId = none` means the sender is absent or hidden. -/
structure LogEntry where
  senderId : Option Int
  recipientId : Int
  timestamp : Int
  deriving DecidableEq, Repr

/-- Return a server-log entry with the recipient ID and timestamp.
Store `none` for the sender ID. -/
def safeLog (_sender : Int) (recipient : Int) (timestamp : Int) : LogEntry :=
  { senderId := none, recipientId := recipient, timestamp := timestamp }

/-- The `sender_id` field of a log entry, or `none` if it is absent or hidden. -/
def adversaryReadSender (entry : LogEntry) : Option Int :=
  entry.senderId

/-- Run the fixed examples. The result is `true` when every observation matches
and `false` otherwise (the Python version raises `AssertionError` instead). -/
def check (candidate : Int → Int → Int → LogEntry) : Bool :=
  (candidate 7 8 1700000000 ==
      ({ senderId := none, recipientId := 8, timestamp := 1700000000 } : LogEntry)) &&
  (candidate 0 2 0 ==
      ({ senderId := none, recipientId := 2, timestamp := 0 } : LogEntry)) &&
  (candidate 7 8 0 ==
      ({ senderId := none, recipientId := 8, timestamp := 0 } : LogEntry)) &&
  (candidate 1 1 1 ==
      ({ senderId := none, recipientId := 1, timestamp := 1 } : LogEntry)) &&
  (candidate 1 8 1700000000 ==
      ({ senderId := none, recipientId := 8, timestamp := 1700000000 } : LogEntry))

/-! ## Security properties -/

/-- The adversary's read of `sender_id` always returns `none`. -/
def HidesSender (f : Int → Int → Int → LogEntry) : Prop :=
  ∀ s r t, adversaryReadSender (f s r t) = none

/-- Noninterference: the whole log entry is independent of the sender. -/
def SenderIndependent (f : Int → Int → Int → LogEntry) : Prop :=
  ∀ s₁ s₂ r t, f s₁ r t = f s₂ r t

/-! ## Basic facts about `safeLog` -/

@[simp] theorem safeLog_senderId (s r t : Int) : (safeLog s r t).senderId = none := rfl

@[simp] theorem safeLog_recipientId (s r t : Int) : (safeLog s r t).recipientId = r := rfl

@[simp] theorem safeLog_timestamp (s r t : Int) : (safeLog s r t).timestamp = t := rfl

theorem safeLog_spec (s r t : Int) :
    safeLog s r t = { senderId := none, recipientId := r, timestamp := t } := rfl

/-- The adversary never learns the sender from a `safeLog` entry. -/
theorem adversary_learns_nothing (s r t : Int) :
    adversaryReadSender (safeLog s r t) = none := rfl

/-- The adversary's view does not depend on who sent the message. -/
theorem adversary_view_independent (s₁ s₂ r t : Int) :
    adversaryReadSender (safeLog s₁ r t) = adversaryReadSender (safeLog s₂ r t) := rfl

/-- No observer that reads the whole entry can tell two senders apart. -/
theorem no_observer_distinguishes_senders {α : Type} (obs : LogEntry → α)
    (s₁ s₂ r t : Int) :
    obs (safeLog s₁ r t) = obs (safeLog s₂ r t) := rfl

theorem safeLog_hidesSender : HidesSender safeLog := by
  intro _ _ _
  rfl

theorem safeLog_senderIndependent : SenderIndependent safeLog := by
  intro _ _ _ _
  rfl

/-- Two `safeLog` entries are equal exactly when their recipients and timestamps
are equal. The senders do not matter. -/
theorem safeLog_eq_iff (s s' r r' t t' : Int) :
    safeLog s r t = safeLog s' r' t' ↔ r = r' ∧ t = t' := by
  constructor
  · intro h
    exact ⟨congrArg LogEntry.recipientId h, congrArg LogEntry.timestamp h⟩
  · intro ⟨hr, ht⟩
    subst hr
    subst ht
    rfl

/-- `safeLog` is the only logger that hides the sender and keeps the recipient and
the timestamp. -/
theorem safeLog_unique (f : Int → Int → Int → LogEntry)
    (hs : ∀ s r t, (f s r t).senderId = none)
    (hr : ∀ s r t, (f s r t).recipientId = r)
    (ht : ∀ s r t, (f s r t).timestamp = t) :
    f = safeLog := by
  funext s r t
  calc f s r t
        = LogEntry.mk (f s r t).senderId (f s r t).recipientId (f s r t).timestamp := rfl
    _ = LogEntry.mk none r t := by rw [hs, hr, ht]
    _ = safeLog s r t := rfl

/-! ## The fixed examples -/

theorem check_safeLog : check safeLog = true := by decide

private theorem and_eq_true_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a
  · simp at h
  · rfl

/-- If a logger passes `check`, it hides the sender on the first example. -/
theorem check_forces_hidden_sender (f : Int → Int → Int → LogEntry)
    (h : check f = true) :
    adversaryReadSender (f 7 8 1700000000) = none := by
  have h1 := and_eq_true_left (and_eq_true_left (and_eq_true_left (and_eq_true_left h)))
  exact congrArg LogEntry.senderId (eq_of_beq h1)

/-! ## Counterexamples -/

/-- A simple logger that records the sender. -/
def unsafeLog (sender recipient timestamp : Int) : LogEntry :=
  { senderId := some sender, recipientId := recipient, timestamp := timestamp }

theorem adversary_reads_unsafeLog (s r t : Int) :
    adversaryReadSender (unsafeLog s r t) = some s := rfl

theorem check_unsafeLog : check unsafeLog = false := by decide

theorem unsafeLog_not_hidesSender : ¬ HidesSender unsafeLog := by
  intro h
  exact absurd (h 0 0 0) (by decide)

/-- A logger that leaks the sender only when the recipient is `3`, an input that
`check` never tests. -/
def leakyLog (sender recipient timestamp : Int) : LogEntry :=
  if recipient = 3 then
    { senderId := some sender, recipientId := recipient, timestamp := timestamp }
  else
    safeLog sender recipient timestamp

theorem check_leakyLog : check leakyLog = true := by decide

theorem leakyLog_leaks : adversaryReadSender (leakyLog 5 3 0) = some 5 := by decide

/-- Passing the fixed examples does not prove that a logger hides the sender. -/
theorem check_does_not_certify_privacy :
    ¬ (∀ f : Int → Int → Int → LogEntry, check f = true → HidesSender f) := by
  intro h
  exact absurd (h leakyLog check_leakyLog 5 3 0) (by decide)

/-- A logger that hides the `sender_id` field but puts the sender in the timestamp. -/
def covertLog (sender recipient _timestamp : Int) : LogEntry :=
  { senderId := none, recipientId := recipient, timestamp := sender }

theorem covertLog_hidesSender : HidesSender covertLog := by
  intro _ _ _
  rfl

/-- Hiding the `sender_id` field is weaker than noninterference: `covertLog` hides
the field, yet its entries still depend on the sender. -/
theorem covertLog_not_senderIndependent : ¬ SenderIndependent covertLog := by
  intro h
  exact absurd (congrArg LogEntry.timestamp (h 0 1 0 0)) (by decide)

#eval if check safeLog then "All tests passed." else "Failed"

end SafeLog

/-
TLDR-end: [safe-log: Lean 4 translation] `safeLog` stores `none` for the sender. The
theorems prove that `check safeLog = true` and that the adversary's read is always `none`.
They also prove that no observer of the entry can tell senders apart, and that `check`
alone cannot certify privacy (`leakyLog`, `covertLog`). This file has not been compiled:
this session had no Lean toolchain.
-/
