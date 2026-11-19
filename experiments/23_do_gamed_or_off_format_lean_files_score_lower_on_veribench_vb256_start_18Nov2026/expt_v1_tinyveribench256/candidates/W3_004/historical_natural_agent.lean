import Mathlib
namespace Agent

/-!
# Safe HMAC length verification

A translation of the Python `safe_hmac_verify` length gate. It accepts exactly
when `mac_len == expected_mac_len`; `message_len` has no effect. This is only a
length check, not a cryptographic verification of the MAC contents.

Python integers are modeled by `Int`, without a nonnegativity restriction:
even negative or zero expected lengths are handled exactly as in the source.
In particular, an empty MAC is rejected when the expected length is nonzero,
but is accepted when the expected length is zero. A longer (extended) or
shorter MAC is rejected. Tests are computational evidence; all named theorems
below have separate kernel-checked proofs.
-/

namespace SafeHMACLength

-- 1. Functional implementation.
def safe_hmac_verify (_message_len mac_len expected_mac_len : Int) : Bool :=
  decide (mac_len = expected_mac_len)

-- 2. The four Python assertions, plus boundary cases for the full Int domain.
example : safe_hmac_verify 10 32 32 = true := by native_decide
example : safe_hmac_verify 10 64 32 = false := by native_decide
example : safe_hmac_verify 10 0 32 = false := by native_decide
example : safe_hmac_verify 10 32 64 = false := by native_decide
example : safe_hmac_verify 10 0 0 = true := by native_decide
example : safe_hmac_verify (-10) (-32) (-32) = true := by native_decide
example : safe_hmac_verify (-10) (-32) 32 = false := by native_decide

-- Executable counterpart of Python's check(), including its success message.
def check : IO Unit := do
  unless safe_hmac_verify 10 32 32 do
    throw (IO.userError "correct length rejected")
  if safe_hmac_verify 10 64 32 then
    throw (IO.userError "wrong mac_len accepted")
  if safe_hmac_verify 10 0 32 then
    throw (IO.userError "empty mac accepted")
  if safe_hmac_verify 10 32 64 then
    throw (IO.userError "mismatched expected accepted")
  IO.println "All tests passed."

#eval check
#eval [safe_hmac_verify 10 32 32, safe_hmac_verify 10 64 32,
  safe_hmac_verify 10 0 32, safe_hmac_verify 10 32 64]

-- 3. The Python function is total on all integer triples.
def Pre (_message_len _mac_len _expected_mac_len : Int) : Prop := True

-- 4. Exact acceptance and rejection characterizations.
def exact_length_prop (message_len mac_len expected_mac_len : Int) : Prop :=
  safe_hmac_verify message_len mac_len expected_mac_len = true ↔
    mac_len = expected_mac_len

theorem exact_length_thm (message_len mac_len expected_mac_len : Int) :
    exact_length_prop message_len mac_len expected_mac_len := by
  simp [exact_length_prop, safe_hmac_verify]

def reject_wrong_length_prop (message_len mac_len expected_mac_len : Int) : Prop :=
  safe_hmac_verify message_len mac_len expected_mac_len = false ↔
    mac_len ≠ expected_mac_len

theorem reject_wrong_length_thm (message_len mac_len expected_mac_len : Int) :
    reject_wrong_length_prop message_len mac_len expected_mac_len := by
  simp [reject_wrong_length_prop, safe_hmac_verify]

def accept_correct_length_prop (message_len expected_mac_len : Int) : Prop :=
  safe_hmac_verify message_len expected_mac_len expected_mac_len = true

theorem accept_correct_length_thm (message_len expected_mac_len : Int) :
    accept_correct_length_prop message_len expected_mac_len := by
  simp [accept_correct_length_prop, safe_hmac_verify]

-- A length extension, of any positive size, cannot pass this gate.
def reject_extension_prop (message_len mac_len expected_mac_len : Int) : Prop :=
  expected_mac_len < mac_len →
    safe_hmac_verify message_len mac_len expected_mac_len = false

theorem reject_extension_thm (message_len mac_len expected_mac_len : Int) :
    reject_extension_prop message_len mac_len expected_mac_len := by
  intro h
  exact (reject_wrong_length_thm message_len mac_len expected_mac_len).2 (ne_of_gt h)

def reject_truncation_prop (message_len mac_len expected_mac_len : Int) : Prop :=
  mac_len < expected_mac_len →
    safe_hmac_verify message_len mac_len expected_mac_len = false

theorem reject_truncation_thm (message_len mac_len expected_mac_len : Int) :
    reject_truncation_prop message_len mac_len expected_mac_len := by
  intro h
  exact (reject_wrong_length_thm message_len mac_len expected_mac_len).2 (ne_of_lt h)

def message_independence_prop
    (message_len other_message_len mac_len expected_mac_len : Int) : Prop :=
  safe_hmac_verify message_len mac_len expected_mac_len =
    safe_hmac_verify other_message_len mac_len expected_mac_len

theorem message_independence_thm
    (message_len other_message_len mac_len expected_mac_len : Int) :
    message_independence_prop message_len other_message_len mac_len expected_mac_len := by
  rfl

-- 5. The postcondition collects the length properties and independence from
-- the current message length (using zero as a canonical alternative length).
-- The theorem above also proves independence for every pair of message lengths.
def Post_prop (message_len mac_len expected_mac_len : Int) : Prop :=
  exact_length_prop message_len mac_len expected_mac_len ∧
  reject_wrong_length_prop message_len mac_len expected_mac_len ∧
  accept_correct_length_prop message_len expected_mac_len ∧
  reject_extension_prop message_len mac_len expected_mac_len ∧
  reject_truncation_prop message_len mac_len expected_mac_len ∧
  message_independence_prop message_len 0 mac_len expected_mac_len

-- 6. Property-based tests. Each check spells out the executable proposition,
-- rather than requiring Decidable instances for the specification definitions.

-- PBT for exact_length_prop.
#eval Plausible.Testable.check (∀ m mac expected : Int,
  (safe_hmac_verify m mac expected = true ↔ mac = expected))

-- PBT for reject_wrong_length_prop.
#eval Plausible.Testable.check (∀ m mac expected : Int,
  (safe_hmac_verify m mac expected = false ↔ mac ≠ expected))

-- PBT for accept_correct_length_prop: deliberately generate equal lengths.
#eval Plausible.Testable.check (∀ m expected : Int,
  safe_hmac_verify m expected expected = true)

-- PBT for reject_extension_prop. Decide the implication itself so that
-- Plausible checks all generated inputs instead of discarding hypotheses.
#eval Plausible.Testable.check (∀ m mac expected : Int,
  decide (expected < mac → safe_hmac_verify m mac expected = false) = true)

-- PBT for reject_truncation_prop.
#eval Plausible.Testable.check (∀ m mac expected : Int,
  decide (mac < expected → safe_hmac_verify m mac expected = false) = true)

-- PBT for message_independence_prop.
#eval Plausible.Testable.check (∀ m other mac expected : Int,
  safe_hmac_verify m mac expected = safe_hmac_verify other mac expected)

-- PBT for the entire Post_prop conjunction, on unrestricted Int inputs.
-- The outer decision evaluates both implications as part of the conjunction.
#eval Plausible.Testable.check (∀ m mac expected : Int,
  decide ((safe_hmac_verify m mac expected = true ↔ mac = expected) ∧
   (safe_hmac_verify m mac expected = false ↔ mac ≠ expected) ∧
   safe_hmac_verify m expected expected = true ∧
   (expected < mac → safe_hmac_verify m mac expected = false) ∧
   (mac < expected → safe_hmac_verify m mac expected = false) ∧
   safe_hmac_verify m mac expected = safe_hmac_verify 0 mac expected) = true)

-- Exhaustive small signed inputs plus common HMAC lengths and their neighbors.
-- This also makes the conditional properties nonvacuous independently of the
-- randomized generators: there are matching, extended, and truncated cases.
def pbtLengths : List Int :=
  (List.range 17).map (fun n => (n : Int) - 8) ++ [10, 31, 32, 33, 63, 64, 65]

-- Bounded PBT for Post_prop (and its five length-related conjuncts).
example : (pbtLengths.all fun m => pbtLengths.all fun mac =>
    pbtLengths.all fun expected =>
      decide ((safe_hmac_verify m mac expected = true ↔ mac = expected) ∧
        (safe_hmac_verify m mac expected = false ↔ mac ≠ expected) ∧
        safe_hmac_verify m expected expected = true ∧
        (expected < mac → safe_hmac_verify m mac expected = false) ∧
        (mac < expected → safe_hmac_verify m mac expected = false) ∧
        safe_hmac_verify m mac expected = safe_hmac_verify 0 mac expected)) = true := by
  native_decide

-- Bounded PBT for message_independence_prop with arbitrary message pairs.
example : (pbtLengths.all fun m => pbtLengths.all fun other =>
    pbtLengths.all fun mac => pbtLengths.all fun expected =>
      safe_hmac_verify m mac expected == safe_hmac_verify other mac expected) = true := by
  native_decide

-- 7. Functional correctness: the unrestricted precondition entails the postcondition.
theorem correctness_thm (message_len mac_len expected_mac_len : Int) :
    Pre message_len mac_len expected_mac_len →
      Post_prop message_len mac_len expected_mac_len := by
  intro _hpre
  exact ⟨exact_length_thm message_len mac_len expected_mac_len,
    reject_wrong_length_thm message_len mac_len expected_mac_len,
    accept_correct_length_thm message_len expected_mac_len,
    reject_extension_thm message_len mac_len expected_mac_len,
    reject_truncation_thm message_len mac_len expected_mac_len,
    message_independence_thm message_len 0 mac_len expected_mac_len⟩

-- 8. Imperative implementation, using a mutable Boolean result.
def safe_hmac_verify_imp (_message_len mac_len expected_mac_len : Int) : Bool :=
  Id.run do
    let mut accepted := false
    if mac_len = expected_mac_len then
      accepted := true
    return accepted

-- 9. Imperative tests corresponding to the Python assertions and boundaries.
example : safe_hmac_verify_imp 10 32 32 = true := by native_decide
example : safe_hmac_verify_imp 10 64 32 = false := by native_decide
example : safe_hmac_verify_imp 10 0 32 = false := by native_decide
example : safe_hmac_verify_imp 10 32 64 = false := by native_decide
example : safe_hmac_verify_imp 10 0 0 = true := by native_decide
example : safe_hmac_verify_imp (-10) (-32) (-32) = true := by native_decide
example : safe_hmac_verify_imp (-10) (-32) 32 = false := by native_decide

#eval [safe_hmac_verify_imp 10 32 32, safe_hmac_verify_imp 10 64 32,
  safe_hmac_verify_imp 10 0 32, safe_hmac_verify_imp 10 32 64]
#eval Plausible.Testable.check (∀ m mac expected : Int,
  safe_hmac_verify m mac expected = safe_hmac_verify_imp m mac expected)

-- 10. Kernel-checked equivalence on the complete Python integer domain.
theorem functional_eq_imperative_thm (message_len mac_len expected_mac_len : Int) :
    safe_hmac_verify message_len mac_len expected_mac_len =
      safe_hmac_verify_imp message_len mac_len expected_mac_len := by
  by_cases h : mac_len = expected_mac_len <;>
    simp [safe_hmac_verify, safe_hmac_verify_imp, h]

end SafeHMACLength
end Agent
