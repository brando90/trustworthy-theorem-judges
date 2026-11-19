import Mathlib
namespace Agent

/-!
# Safe sealed-sender logging

A translation of the Python sealed-sender server log. The dictionary has a
fixed schema, represented by `LogEntry`; Python integers are unbounded signed
`Int`s, and Python `None` in the sender field is `Option.none`. Since this
schema always contains `sender_id`, reading the field implements the Python
`entry.get("sender_id")` on every entry produced by either implementation.

The server log hides the sender but preserves the recipient and timestamp.
We also prove that changing only the sender leaves the entire entry unchanged.
This models the logging interface, not encryption itself, and makes no claim
of protection against global passive traffic analysis.
-/

namespace «96_unsafeMetadataProtection_safe»

/-! ## Functional implementation -/

structure LogEntry where
  sender_id : Option Int
  recipient_id : Int
  timestamp : Int
  deriving Repr, DecidableEq

/-- The sender argument is deliberately unused. -/
def safe_log (_sender recipient timestamp : Int) : LogEntry :=
  { sender_id := none, recipient_id := recipient, timestamp := timestamp }

def adversary_read_sender (entry : LogEntry) : Option Int :=
  entry.sender_id

/-- The Boolean success condition of all assertions in Python's `check`.
Comparing the optional sender with `some 42` models comparison with Python's
integer `42`; `none` is distinct from every integer. -/
def check (candidate : Int → Int → Int → LogEntry) : Bool :=
  let entry := candidate 7 8 1700000000
  decide (
    adversary_read_sender entry = none ∧
    entry.recipient_id = 8 ∧
    entry.timestamp = 1700000000 ∧
    adversary_read_sender (candidate 0 8 1) = none ∧
    adversary_read_sender (candidate 99999 1 0) = none ∧
    adversary_read_sender (candidate 42 1 1) ≠ some 42)

/-! ## Unit tests -/

example : adversary_read_sender (safe_log 7 8 1700000000) = none := by
  native_decide
example : (safe_log 7 8 1700000000).recipient_id = 8 := by
  native_decide
example : (safe_log 7 8 1700000000).timestamp = 1700000000 := by
  native_decide
example : adversary_read_sender (safe_log 0 8 1) = none := by
  native_decide
example : adversary_read_sender (safe_log 99999 1 0) = none := by
  native_decide
example : adversary_read_sender (safe_log 42 1 1) ≠ some 42 := by
  native_decide
example : safe_log (-99999) (-8) (-1700000000) =
    { sender_id := none, recipient_id := -8, timestamp := -1700000000 } := by
  native_decide
example : check safe_log = true := by
  native_decide

#eval safe_log 7 8 1700000000
#eval adversary_read_sender (safe_log 42 1 1)
#eval check safe_log

/-! ## Precondition and proved properties -/

/-- Python imposes no restrictions on any of its three integer arguments. -/
def Pre (_sender _recipient _timestamp : Int) : Prop := True

def sender_hidden_prop (sender recipient timestamp : Int) : Prop :=
  adversary_read_sender (safe_log sender recipient timestamp) = none

theorem sender_hidden_thm (sender recipient timestamp : Int) :
    sender_hidden_prop sender recipient timestamp := by
  rfl

def recipient_visible_prop (sender recipient timestamp : Int) : Prop :=
  (safe_log sender recipient timestamp).recipient_id = recipient

theorem recipient_visible_thm (sender recipient timestamp : Int) :
    recipient_visible_prop sender recipient timestamp := by
  rfl

def timestamp_recorded_prop (sender recipient timestamp : Int) : Prop :=
  (safe_log sender recipient timestamp).timestamp = timestamp

theorem timestamp_recorded_thm (sender recipient timestamp : Int) :
    timestamp_recorded_prop sender recipient timestamp := by
  rfl

/-- The hidden field is not the actual sender, including sender zero. -/
def sender_not_actual_prop (sender recipient timestamp : Int) : Prop :=
  adversary_read_sender (safe_log sender recipient timestamp) ≠ some sender

theorem sender_not_actual_thm (sender recipient timestamp : Int) :
    sender_not_actual_prop sender recipient timestamp := by
  simp [sender_not_actual_prop, adversary_read_sender, safe_log]

/-- Noninterference: with public metadata fixed, no part of the entry depends
on which sender supplied the message. -/
def sender_independent_prop (sender otherSender recipient timestamp : Int) : Prop :=
  safe_log sender recipient timestamp = safe_log otherSender recipient timestamp

theorem sender_independent_thm (sender otherSender recipient timestamp : Int) :
    sender_independent_prop sender otherSender recipient timestamp := by
  rfl

/-- Kernel-checked proof of the original Python test harness's success. -/
theorem check_safe_log_thm : check safe_log = true := by
  decide

/-! ## Postcondition -/

def Post_prop (sender recipient timestamp : Int) : Prop :=
  sender_hidden_prop sender recipient timestamp ∧
  recipient_visible_prop sender recipient timestamp ∧
  timestamp_recorded_prop sender recipient timestamp ∧
  sender_not_actual_prop sender recipient timestamp ∧
  (∀ otherSender : Int, sender_independent_prop sender otherSender recipient timestamp)

/-! ## Property-based tests

Each check below spells out the executable form of the named property over
arbitrary signed integers. These are tests, not proofs. For the postcondition,
the arbitrary `otherSender` also samples its universally quantified final
conjunct; no decidability of a universal `Prop` definition is assumed.
-/

-- PBT: sender_hidden_prop.
#eval Plausible.Testable.check (∀ sender recipient timestamp : Int,
  adversary_read_sender (safe_log sender recipient timestamp) = none)

-- PBT: recipient_visible_prop.
#eval Plausible.Testable.check (∀ sender recipient timestamp : Int,
  (safe_log sender recipient timestamp).recipient_id = recipient)

-- PBT: timestamp_recorded_prop.
#eval Plausible.Testable.check (∀ sender recipient timestamp : Int,
  (safe_log sender recipient timestamp).timestamp = timestamp)

-- PBT: sender_not_actual_prop.
#eval Plausible.Testable.check (∀ sender recipient timestamp : Int,
  adversary_read_sender (safe_log sender recipient timestamp) ≠ some sender)

-- PBT: sender_independent_prop.
#eval Plausible.Testable.check (∀ sender otherSender recipient timestamp : Int,
  safe_log sender recipient timestamp = safe_log otherSender recipient timestamp)

-- PBT: Post_prop, including its sender-independence conjunct.
#eval Plausible.Testable.check (∀ sender recipient timestamp otherSender : Int,
  adversary_read_sender (safe_log sender recipient timestamp) = none ∧
  (safe_log sender recipient timestamp).recipient_id = recipient ∧
  (safe_log sender recipient timestamp).timestamp = timestamp ∧
  adversary_read_sender (safe_log sender recipient timestamp) ≠ some sender ∧
  safe_log sender recipient timestamp = safe_log otherSender recipient timestamp)

/-! ## Correctness -/

theorem correctness_thm (sender recipient timestamp : Int) :
    Pre sender recipient timestamp → Post_prop sender recipient timestamp := by
  intro _
  exact ⟨sender_hidden_thm sender recipient timestamp,
    recipient_visible_thm sender recipient timestamp,
    timestamp_recorded_thm sender recipient timestamp,
    sender_not_actual_thm sender recipient timestamp,
    fun otherSender => sender_independent_thm sender otherSender recipient timestamp⟩

/-! ## Imperative implementation -/

/-- Construct the same log by updating mutable state. The initial and all
subsequent states keep the sender field hidden. -/
def safe_log_imperative (_sender recipient timestamp : Int) : LogEntry := Id.run do
  let mut entry : LogEntry :=
    { sender_id := none, recipient_id := 0, timestamp := 0 }
  entry := { entry with recipient_id := recipient }
  entry := { entry with timestamp := timestamp }
  return entry

/-! ## Imperative tests -/

example : adversary_read_sender (safe_log_imperative 7 8 1700000000) = none := by
  native_decide
example : (safe_log_imperative 7 8 1700000000).recipient_id = 8 := by
  native_decide
example : (safe_log_imperative 7 8 1700000000).timestamp = 1700000000 := by
  native_decide
example : adversary_read_sender (safe_log_imperative 0 8 1) = none := by
  native_decide
example : adversary_read_sender (safe_log_imperative 99999 1 0) = none := by
  native_decide
example : adversary_read_sender (safe_log_imperative 42 1 1) ≠ some 42 := by
  native_decide
example : safe_log_imperative (-99999) (-8) (-1700000000) =
    { sender_id := none, recipient_id := -8, timestamp := -1700000000 } := by
  native_decide
example : check safe_log_imperative = true := by
  native_decide

#eval safe_log_imperative 7 8 1700000000
#eval check safe_log_imperative
#eval Plausible.Testable.check (∀ sender recipient timestamp : Int,
  safe_log sender recipient timestamp = safe_log_imperative sender recipient timestamp)

/-! ## Functional-imperative equivalence -/

theorem functional_imperative_equivalence_thm (sender recipient timestamp : Int) :
    safe_log sender recipient timestamp = safe_log_imperative sender recipient timestamp := by
  rfl

end «96_unsafeMetadataProtection_safe»
end Agent
