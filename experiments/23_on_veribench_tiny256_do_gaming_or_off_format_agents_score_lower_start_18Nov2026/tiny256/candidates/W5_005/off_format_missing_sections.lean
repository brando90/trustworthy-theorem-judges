import Mathlib

namespace Gold.UnsafeServerReadsPlaintext

def unsafeServerRead (serverHasSessionKey : Bool) (message : Nat) : Option Nat :=
  if serverHasSessionKey then some message else none

example : unsafeServerRead true 12345 = some 12345 := by native_decide
example : unsafeServerRead false 12345 = none := by native_decide
example : unsafeServerRead true 0 = some 0 := by native_decide
example : unsafeServerRead false 0 = none := by native_decide
example : unsafeServerRead true 42 = some 42 := by native_decide
example : unsafeServerRead true 99999 = some 99999 := by native_decide
example : unsafeServerRead true 12345 ≠ none := by native_decide

theorem read_with_key_returns_message (message : Nat) :
    unsafeServerRead true message = some message := by
  simp [unsafeServerRead]

theorem keyed_server_is_not_blind :
    ∃ message : Nat, unsafeServerRead true message ≠ none :=
  ⟨42, by simp [unsafeServerRead]⟩

theorem keyed_server_recovers_exact_plaintext :
    ∀ message : Nat, ∃ result, unsafeServerRead true message = some result ∧ result = message := by
  intro message
  exact ⟨message, by simp [unsafeServerRead], rfl⟩

end Gold.UnsafeServerReadsPlaintext
