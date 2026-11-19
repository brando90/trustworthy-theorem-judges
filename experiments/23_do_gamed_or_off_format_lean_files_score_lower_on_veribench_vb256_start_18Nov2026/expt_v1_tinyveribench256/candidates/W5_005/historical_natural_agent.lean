import Mathlib
namespace Agent

/-!
# Unsafe TLS: the server reads plaintext

Translation of `unsafe_server_read` and its Python checks. `Bool` represents
possession of the session key, and `Int` preserves Python's unbounded signed
integer message domain. A server holding the key returns the entire message;
without the key it returns the sentinel `-1`. TLS normally uses the keyed case,
so this model exposes every plaintext to the server, including a compromised
or legally compelled server. No cryptographic operation is being modeled.

Both key states remain admissible. In particular, `-1` is also a valid message:
observing the sentinel alone does not establish that the server lacked a key.
The bounded executable tests are evidence; all named theorems have separate
kernel-checkable proofs.
-/

namespace UnsafeServerReadsPlaintext

/-! ## Functional implementation -/

/-- The Python branch order: reject a missing key, otherwise return plaintext. -/
def unsafe_server_read (server_has_session_key : Bool) (message : Int) : Int :=
  if !server_has_session_key then -1 else message

/-! ## Unit tests and the original check suite -/

/-- Executable conjunction of the five assertions in Python's `check`. -/
def check (candidate : Bool → Int → Int) : Bool :=
  candidate true 12345 == 12345 &&
  candidate true 0 == 0 &&
  candidate true 99999 == 99999 &&
  candidate true 42 == 42 &&
  candidate false 12345 == (-1 : Int)

example : unsafe_server_read true 12345 = 12345 := by native_decide
example : unsafe_server_read true 0 = 0 := by native_decide
example : unsafe_server_read true 99999 = 99999 := by native_decide
example : unsafe_server_read true 42 = 42 := by native_decide
example : unsafe_server_read false 12345 = -1 := by native_decide
example : unsafe_server_read true (-57) = -57 := by native_decide
example : unsafe_server_read true (-1) = -1 := by native_decide
example : unsafe_server_read false 0 = -1 := by native_decide
example : unsafe_server_read false (-57) = -1 := by native_decide
example : check unsafe_server_read = true := by native_decide

#eval unsafe_server_read true 12345
#eval unsafe_server_read false 12345
#eval check unsafe_server_read
#eval if check unsafe_server_read then "All tests passed." else "Candidate failed tests"

/-! ## Preconditions -/

/-- The source function imposes no restriction on either typed input. -/
def Pre (_server_has_session_key : Bool) (_message : Int) : Prop := True

/-! ## Properties and their proofs -/

/-- Possessing the session key exposes the exact plaintext, for any integer. -/
def keyed_read_prop (server_has_session_key : Bool) (message : Int) : Prop :=
  server_has_session_key = true →
    unsafe_server_read server_has_session_key message = message

theorem keyed_read_thm (server_has_session_key : Bool) (message : Int) :
    keyed_read_prop server_has_session_key message := by
  unfold keyed_read_prop
  intro h
  subst server_has_session_key
  rfl

/-- In the usual TLS setting the server can read every message. -/
theorem tls_server_reads_all_messages_thm (message : Int) :
    unsafe_server_read true message = message := by
  rfl

/-- A server lacking the key returns the sentinel regardless of the message. -/
def keyless_read_prop (server_has_session_key : Bool) (message : Int) : Prop :=
  server_has_session_key = false →
    unsafe_server_read server_has_session_key message = -1

theorem keyless_read_thm (server_has_session_key : Bool) (message : Int) :
    keyless_read_prop server_has_session_key message := by
  unfold keyless_read_prop
  intro h
  subst server_has_session_key
  rfl

/-- Complete input/output behavior, including both key states. -/
def exact_result_prop (server_has_session_key : Bool) (message : Int) : Prop :=
  unsafe_server_read server_has_session_key message =
    (if server_has_session_key then message else -1)

theorem exact_result_thm (server_has_session_key : Bool) (message : Int) :
    exact_result_prop server_has_session_key message := by
  cases server_has_session_key <;> rfl

/-! ## Postcondition -/

def Post_prop (server_has_session_key : Bool) (message : Int) : Prop :=
  keyed_read_prop server_has_session_key message ∧
  keyless_read_prop server_has_session_key message ∧
  exact_result_prop server_has_session_key message

/-! ## Bounded property-based tests

Exhaust both key states and all integers from -128 through 128, supplemented
by larger positive and negative values. Each test spells out the executable
Boolean form of the named property; no `Decidable` instances for the property
definitions are needed. No theorem below depends on these native tests.
-/

def pbtMessages : List Int :=
  (List.range 257).map (fun n => (n : Int) - 128) ++
    [-99999, -12345, 12345, 99999]

-- PBT for keyed_read_prop (also tests the TLS all-messages specialization).
example :
    ([false, true] : List Bool).all (fun hasKey =>
      pbtMessages.all (fun message =>
        !hasKey || (unsafe_server_read hasKey message == message))) = true := by
  native_decide

-- PBT for keyless_read_prop.
example :
    ([false, true] : List Bool).all (fun hasKey =>
      pbtMessages.all (fun message =>
        hasKey || (unsafe_server_read hasKey message == (-1 : Int)))) = true := by
  native_decide

-- PBT for exact_result_prop.
example :
    ([false, true] : List Bool).all (fun hasKey =>
      pbtMessages.all (fun message =>
        unsafe_server_read hasKey message ==
          (if hasKey then message else (-1 : Int)))) = true := by
  native_decide

-- PBT for the entire Post_prop conjunction. Pre is true on all these inputs.
example :
    ([false, true] : List Bool).all (fun hasKey =>
      pbtMessages.all (fun message =>
        (!hasKey || (unsafe_server_read hasKey message == message)) &&
        (hasKey || (unsafe_server_read hasKey message == (-1 : Int))) &&
        (unsafe_server_read hasKey message ==
          (if hasKey then message else (-1 : Int))))) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (server_has_session_key : Bool) (message : Int) :
    Pre server_has_session_key message →
      Post_prop server_has_session_key message := by
  intro _
  exact ⟨keyed_read_thm server_has_session_key message,
    keyless_read_thm server_has_session_key message,
    exact_result_thm server_has_session_key message⟩

/-! ## Imperative implementation -/

/-- Mutable-state version: start with the sentinel and overwrite it if keyed. -/
def unsafe_server_read_imperative
    (server_has_session_key : Bool) (message : Int) : Int := Id.run do
  let mut result : Int := -1
  if server_has_session_key then
    result := message
  return result

/-! ## Imperative tests -/

example : unsafe_server_read_imperative true 12345 = 12345 := by native_decide
example : unsafe_server_read_imperative true 0 = 0 := by native_decide
example : unsafe_server_read_imperative true 99999 = 99999 := by native_decide
example : unsafe_server_read_imperative true 42 = 42 := by native_decide
example : unsafe_server_read_imperative false 12345 = -1 := by native_decide
example : unsafe_server_read_imperative true (-57) = -57 := by native_decide
example : unsafe_server_read_imperative true (-1) = -1 := by native_decide
example : unsafe_server_read_imperative false 0 = -1 := by native_decide
example : unsafe_server_read_imperative false (-57) = -1 := by native_decide
example : check unsafe_server_read_imperative = true := by native_decide

#eval unsafe_server_read_imperative true 42
#eval unsafe_server_read_imperative false 12345
#eval check unsafe_server_read_imperative

/-! ## Equivalence on the full input domain -/

theorem functional_imperative_equivalence_thm
    (server_has_session_key : Bool) (message : Int) :
    unsafe_server_read server_has_session_key message =
      unsafe_server_read_imperative server_has_session_key message := by
  cases server_has_session_key <;> rfl

end UnsafeServerReadsPlaintext
end Agent
