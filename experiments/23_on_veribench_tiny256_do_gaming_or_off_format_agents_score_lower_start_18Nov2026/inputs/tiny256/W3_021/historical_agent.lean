import Mathlib
namespace Agent

/-!
# Safe stack canary check

Translation of `safe_stack_canary_bypass` and its Python regression tests.
Python's unbounded integers are represented by `Int`. All strings and all
integer canaries are admissible. The payload is intentionally unused: success
is returned exactly when the actual and expected canaries agree.

The specifications establish acceptance, rejection, and independence from the
payload. Bounded executable tests supplement, but do not replace, the general
kernel-checked proofs. A mutable implementation performs the check before
returning, and is proved equivalent to the functional implementation.
-/

namespace «147_unsafeStackCanaryBypass_safe»

-- Functional implementation.
def safe_stack_canary_bypass (_user_data : String)
    (canary expected_canary : Int) : Bool :=
  decide (canary = expected_canary)

-- The four original Python unit tests.
example : safe_stack_canary_bypass "hello" 0xDEADBEEF 0xDEADBEEF = true := by
  native_decide

example : safe_stack_canary_bypass "data" 12345 12345 = true := by
  native_decide

example : safe_stack_canary_bypass "overflow_payload" 0x41414141 0xDEADBEEF = false := by
  native_decide

example : safe_stack_canary_bypass "exploit" 0 0xDEADBEEF = false := by
  native_decide

-- Additional regression cases ensure that Int, not an unsigned machine word,
-- models the source domain.
example : safe_stack_canary_bypass "" (-7) (-7) = true := by
  native_decide

example : safe_stack_canary_bypass "negative" (-7) 7 = false := by
  native_decide

example : safe_stack_canary_bypass "large" 18446744073709551616
    18446744073709551616 = true := by
  native_decide

def check : IO Unit := do
  unless safe_stack_canary_bypass "hello" 0xDEADBEEF 0xDEADBEEF do
    throw (IO.userError "valid canary rejected")
  unless safe_stack_canary_bypass "data" 12345 12345 do
    throw (IO.userError "valid canary rejected")
  if safe_stack_canary_bypass "overflow_payload" 0x41414141 0xDEADBEEF then
    throw (IO.userError "tampered canary accepted")
  if safe_stack_canary_bypass "exploit" 0 0xDEADBEEF then
    throw (IO.userError "zeroed canary accepted")
  IO.println "All tests passed."

#eval check

-- No restrictions on the payload, sign, or magnitude of either integer.
def Pre (_user_data : String) (_canary _expected_canary : Int) : Prop := True

-- Acceptance is both sound and complete: precisely matching canaries succeed.
def acceptance_prop (user_data : String) (canary expected_canary : Int) : Prop :=
  safe_stack_canary_bypass user_data canary expected_canary = true ↔
    canary = expected_canary

theorem acceptance_thm (user_data : String) (canary expected_canary : Int) :
    acceptance_prop user_data canary expected_canary := by
  simp [acceptance_prop, safe_stack_canary_bypass]

-- Every tampered canary is rejected, and only tampered canaries are rejected.
def rejection_prop (user_data : String) (canary expected_canary : Int) : Prop :=
  safe_stack_canary_bypass user_data canary expected_canary = false ↔
    canary ≠ expected_canary

theorem rejection_thm (user_data : String) (canary expected_canary : Int) :
    rejection_prop user_data canary expected_canary := by
  simp [rejection_prop, safe_stack_canary_bypass]

-- Changing the payload cannot bypass (or otherwise change) the canary check.
def payload_independence_prop (user_data : String)
    (canary expected_canary : Int) : Prop :=
  ∀ other_data : String,
    safe_stack_canary_bypass user_data canary expected_canary =
      safe_stack_canary_bypass other_data canary expected_canary

theorem payload_independence_thm (user_data : String)
    (canary expected_canary : Int) :
    payload_independence_prop user_data canary expected_canary := by
  intro other_data
  rfl

-- The postcondition combines all three guarantees for the actual result.
def Post_prop (user_data : String) (canary expected_canary : Int) : Prop :=
  acceptance_prop user_data canary expected_canary ∧
  rejection_prop user_data canary expected_canary ∧
  payload_independence_prop user_data canary expected_canary

-- Property-based tests: exhaustive products of a bounded signed range,
-- representative large integers, and several payloads. These bounds restrict
-- only the tests; none of the specifications or proofs restrict the inputs.
private def canarySamples : List Int :=
  ((List.range 41).map (fun n => (n : Int) - 20)) ++
    [12345, 0xDEADBEEF, 0x41414141,
      18446744073709551616, -18446744073709551616]

private def payloadSamples : List String :=
  ["", "hello", "data", "overflow_payload", "exploit", "Unicode: λ"]

private def testInputs (test : String → Int → Int → Bool) : Bool :=
  payloadSamples.all fun data =>
    canarySamples.all fun canary =>
      canarySamples.all fun expected => test data canary expected

-- PBT for acceptance_prop, using its executable pointwise form.
example : testInputs (fun data canary expected =>
    decide (safe_stack_canary_bypass data canary expected = true ↔
      canary = expected)) = true := by
  native_decide

-- PBT for rejection_prop.
example : testInputs (fun data canary expected =>
    decide (safe_stack_canary_bypass data canary expected = false ↔
      canary ≠ expected)) = true := by
  native_decide

-- PBT for payload_independence_prop: enumerate both payload arguments.
example : testInputs (fun data canary expected =>
    payloadSamples.all fun other =>
      safe_stack_canary_bypass data canary expected ==
        safe_stack_canary_bypass other canary expected) = true := by
  native_decide

-- PBT for Post_prop: the executable conjunction of all three guarantees,
-- with the universally quantified alternate payload sampled from the list.
example : testInputs (fun data canary expected =>
    let result := safe_stack_canary_bypass data canary expected
    decide (result = true ↔ canary = expected) &&
    decide (result = false ↔ canary ≠ expected) &&
    payloadSamples.all (fun other =>
      result == safe_stack_canary_bypass other canary expected)) = true := by
  native_decide

-- General correctness, with the original unrestricted input domain.
theorem correctness_thm (user_data : String) (canary expected_canary : Int) :
    Pre user_data canary expected_canary →
      Post_prop user_data canary expected_canary := by
  intro _hpre
  exact ⟨acceptance_thm user_data canary expected_canary,
    rejection_thm user_data canary expected_canary,
    payload_independence_thm user_data canary expected_canary⟩

-- Imperative implementation: start in the rejecting state and permit success
-- only after checking equality, before the function returns.
def safe_stack_canary_bypass_imp (_user_data : String)
    (canary expected_canary : Int) : Bool := Id.run do
  let mut accepted := false
  if canary = expected_canary then
    accepted := true
  return accepted

-- Imperative regression tests.
example : safe_stack_canary_bypass_imp "hello" 0xDEADBEEF 0xDEADBEEF = true := by
  native_decide

example : safe_stack_canary_bypass_imp "data" 12345 12345 = true := by
  native_decide

example : safe_stack_canary_bypass_imp "overflow_payload" 0x41414141 0xDEADBEEF = false := by
  native_decide

example : safe_stack_canary_bypass_imp "exploit" 0 0xDEADBEEF = false := by
  native_decide

#eval [safe_stack_canary_bypass_imp "hello" 0xDEADBEEF 0xDEADBEEF,
  safe_stack_canary_bypass_imp "data" 12345 12345,
  safe_stack_canary_bypass_imp "overflow_payload" 0x41414141 0xDEADBEEF,
  safe_stack_canary_bypass_imp "exploit" 0 0xDEADBEEF]

-- Additional bounded evidence for equivalence, including negative and large
-- integers; the universal proof below does not depend on this test.
example : testInputs (fun data canary expected =>
    safe_stack_canary_bypass data canary expected ==
      safe_stack_canary_bypass_imp data canary expected) = true := by
  native_decide

theorem equivalence_thm (user_data : String) (canary expected_canary : Int) :
    safe_stack_canary_bypass user_data canary expected_canary =
      safe_stack_canary_bypass_imp user_data canary expected_canary := by
  by_cases h : canary = expected_canary <;>
    simp [safe_stack_canary_bypass, safe_stack_canary_bypass_imp, h]

end «147_unsafeStackCanaryBypass_safe»
end Agent
