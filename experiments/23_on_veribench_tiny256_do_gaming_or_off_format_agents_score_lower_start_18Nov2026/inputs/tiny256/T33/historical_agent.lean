import Mathlib
namespace Agent

/-!
# Safe end-to-end encryption: the server is always blind

Translation of the Python model accompanying MIT 6.858 Lecture 14.
The server's observation is always the ciphertext sentinel `-1`, independently
of its state and the message. A recipient possessing its private key receives
the message; a recipient without the key receives only the sentinel.

Python integers are modeled by `Int`, without bounds or sign restrictions.
This is an observation model, not an implementation of cryptographic primitives.
In particular, `-1` is also a valid plaintext: an output equal to the message
does not, by itself, establish possession of the private key.
The Python assertion-based checkers are represented as Boolean conjunctions;
the tests below assert that these conjunctions hold.
-/

namespace «104_unsafeServerReadsPlaintext_safe»

/-! ## Functional implementation -/

def safe_e2e_server_sees (_server_state : Int) (_message : Int) : Int :=
  -1

def safe_e2e_recipient_reads (recipient_has_private_key : Bool) (message : Int) : Int :=
  if recipient_has_private_key then message else -1

def check_server (candidate : Int → Int → Int) : Bool :=
  (candidate 0 12345 == (-1 : Int)) &&
  (candidate 0 0 == (-1 : Int)) &&
  (candidate 999 42 == (-1 : Int)) &&
  (candidate 0 100 == candidate 999 100)

def check_recipient (candidate : Bool → Int → Int) : Bool :=
  (candidate true 12345 == (12345 : Int)) &&
  (candidate false 12345 == (-1 : Int)) &&
  (candidate true 0 == (0 : Int)) &&
  (candidate true 99999 == (99999 : Int))

/-! ## Unit tests and the Python public checks -/

example : safe_e2e_server_sees 0 12345 = -1 := by native_decide
example : safe_e2e_server_sees 0 0 = -1 := by native_decide
example : safe_e2e_server_sees 999 42 = -1 := by native_decide
example : safe_e2e_server_sees 0 100 = safe_e2e_server_sees 999 100 := by native_decide

example : safe_e2e_recipient_reads true 12345 = 12345 := by native_decide
example : safe_e2e_recipient_reads false 12345 = -1 := by native_decide
example : safe_e2e_recipient_reads true 0 = 0 := by native_decide
example : safe_e2e_recipient_reads true 99999 = 99999 := by native_decide

-- Negative messages and the sentinel itself remain admissible plaintexts.
example : safe_e2e_server_sees (-999) (-12345) = -1 := by native_decide
example : safe_e2e_recipient_reads true (-12345) = -12345 := by native_decide
example : safe_e2e_recipient_reads false (-12345) = -1 := by native_decide
example : safe_e2e_recipient_reads true (-1) = -1 := by native_decide

example : check_server safe_e2e_server_sees = true := by native_decide
example : check_recipient safe_e2e_recipient_reads = true := by native_decide

#eval safe_e2e_server_sees 999 42
#eval safe_e2e_recipient_reads true 12345
#eval safe_e2e_recipient_reads false 12345
#eval if check_server safe_e2e_server_sees && check_recipient safe_e2e_recipient_reads
      then "All tests passed." else "Check failed."

/-! ## Preconditions and universally proved properties -/

-- The source program imposes no restrictions on state, key flag, or message.
def Pre (_server_state : Int) (_recipient_has_private_key : Bool) (_message : Int) : Prop :=
  True

def server_blind_prop (server_state message : Int) : Prop :=
  safe_e2e_server_sees server_state message = -1

theorem server_blind_thm (server_state message : Int) :
    server_blind_prop server_state message := by
  rfl

def server_state_independent_prop (state₁ state₂ message : Int) : Prop :=
  safe_e2e_server_sees state₁ message = safe_e2e_server_sees state₂ message

theorem server_state_independent_thm (state₁ state₂ message : Int) :
    server_state_independent_prop state₁ state₂ message := by
  rfl

def recipient_with_key_prop (recipient_has_private_key : Bool) (message : Int) : Prop :=
  recipient_has_private_key = true →
    safe_e2e_recipient_reads recipient_has_private_key message = message

theorem recipient_with_key_thm (recipient_has_private_key : Bool) (message : Int) :
    recipient_with_key_prop recipient_has_private_key message := by
  intro h
  simp [safe_e2e_recipient_reads, h]

def recipient_without_key_prop (recipient_has_private_key : Bool) (message : Int) : Prop :=
  recipient_has_private_key = false →
    safe_e2e_recipient_reads recipient_has_private_key message = -1

theorem recipient_without_key_thm (recipient_has_private_key : Bool) (message : Int) :
    recipient_without_key_prop recipient_has_private_key message := by
  intro h
  simp [safe_e2e_recipient_reads, h]

/-! ## Post-condition -/

def Post_prop (server_state : Int) (recipient_has_private_key : Bool) (message : Int) : Prop :=
  server_blind_prop server_state message ∧
  (∀ other_state : Int, server_state_independent_prop server_state other_state message) ∧
  recipient_with_key_prop recipient_has_private_key message ∧
  recipient_without_key_prop recipient_has_private_key message

/-! ## Bounded property-based tests

These exhaustively check signed small integers, both Boolean values, and some
larger representative integers. They are executable evidence, not ingredients
of any theorem proof. All theorem statements retain the full `Int` domain.
-/

def pbtInts : List Int :=
  (List.range 41).map (fun n => (n : Int) - 20) ++
    [-99999, -12345, -999, 42, 100, 999, 12345, 99999]

-- PBT for server_blind_prop.
example :
    (pbtInts.all fun state =>
      pbtInts.all fun message =>
        safe_e2e_server_sees state message == (-1 : Int)) = true := by
  native_decide

-- PBT for server_state_independent_prop, varying both states independently.
example :
    (pbtInts.all fun state₁ =>
      pbtInts.all fun state₂ =>
        pbtInts.all fun message =>
          safe_e2e_server_sees state₁ message ==
            safe_e2e_server_sees state₂ message) = true := by
  native_decide

-- PBT for recipient_with_key_prop: !hasKey || result == message.
example :
    (([false, true] : List Bool).all fun hasKey =>
      pbtInts.all fun message =>
        (!hasKey || (safe_e2e_recipient_reads hasKey message == message))) = true := by
  native_decide

-- PBT for recipient_without_key_prop: hasKey || result == -1.
example :
    (([false, true] : List Bool).all fun hasKey =>
      pbtInts.all fun message =>
        (hasKey || (safe_e2e_recipient_reads hasKey message == (-1 : Int)))) = true := by
  native_decide

-- PBT for Post_prop. The universal other_state clause is checked over the
-- same independent bounded domain as the standalone state-independence test.
-- Pre is True, so no samples are discarded or excluded by a precondition.
example :
    (pbtInts.all fun state =>
      pbtInts.all fun other_state =>
        ([false, true] : List Bool).all fun hasKey =>
          pbtInts.all fun message =>
            (safe_e2e_server_sees state message == (-1 : Int)) &&
            (safe_e2e_server_sees state message ==
              safe_e2e_server_sees other_state message) &&
            (!hasKey || (safe_e2e_recipient_reads hasKey message == message)) &&
            (hasKey || (safe_e2e_recipient_reads hasKey message == (-1 : Int)))) = true := by
  native_decide

/-! ## Correctness for all admissible inputs -/

theorem correctness_thm (server_state : Int) (recipient_has_private_key : Bool)
    (message : Int) :
    Pre server_state recipient_has_private_key message →
      Post_prop server_state recipient_has_private_key message := by
  intro _
  exact ⟨server_blind_thm server_state message,
    fun other_state => server_state_independent_thm server_state other_state message,
    recipient_with_key_thm recipient_has_private_key message,
    recipient_without_key_thm recipient_has_private_key message⟩

/-! ## Imperative implementation with mutable local return slots -/

def safe_e2e_server_sees_imperative (_server_state : Int) (_message : Int) : Int := Id.run do
  let mut result : Int := 0
  result := -1
  return result

def safe_e2e_recipient_reads_imperative (recipient_has_private_key : Bool)
    (message : Int) : Int := Id.run do
  let mut result : Int := -1
  if recipient_has_private_key then
    result := message
  return result

/-! ## Imperative tests -/

-- Reuse every original assertion with the imperative functions as candidates.
example : check_server safe_e2e_server_sees_imperative = true := by native_decide
example : check_recipient safe_e2e_recipient_reads_imperative = true := by native_decide
example : safe_e2e_server_sees_imperative (-999) (-12345) = -1 := by native_decide
example : safe_e2e_recipient_reads_imperative true (-12345) = -12345 := by native_decide
example : safe_e2e_recipient_reads_imperative false (-12345) = -1 := by native_decide
example : safe_e2e_recipient_reads_imperative true (-1) = -1 := by native_decide

#eval check_server safe_e2e_server_sees_imperative
#eval check_recipient safe_e2e_recipient_reads_imperative
#eval safe_e2e_recipient_reads_imperative true 99999
#eval safe_e2e_recipient_reads_imperative false 99999

/-! ## Functional/imperative equivalence over the full input domains -/

theorem server_equivalence_thm :
    safe_e2e_server_sees = safe_e2e_server_sees_imperative := by
  funext server_state message
  rfl

theorem recipient_equivalence_thm :
    safe_e2e_recipient_reads = safe_e2e_recipient_reads_imperative := by
  funext recipient_has_private_key message
  cases recipient_has_private_key <;> rfl

theorem equivalence_thm :
    (safe_e2e_server_sees = safe_e2e_server_sees_imperative) ∧
    (safe_e2e_recipient_reads = safe_e2e_recipient_reads_imperative) := by
  exact ⟨server_equivalence_thm, recipient_equivalence_thm⟩

end «104_unsafeServerReadsPlaintext_safe»
end Agent
