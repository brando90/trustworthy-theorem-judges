import Mathlib
namespace Agent

/-!
# Safe DNS reply validation

Translation of the Python `safe_dns_reply` and its checks. A reply is accepted
exactly when both its query ID and its source port match the expected values.
`Int` preserves Python's arbitrary-precision integer domain: the source does
not enforce a 16-bit range. Rejection of either mismatch is the validation
property; no probabilistic guarantee about an attack is assumed.
-/

namespace «87_unsafeDNSReply_safe»

/-- Functional translation of Python's conjunction of two integer equalities. -/
def safe_dns_reply (query_id expected_id src_port expected_port : Int) : Bool :=
  (query_id == expected_id) && (src_port == expected_port)

-- The four original unit tests.
example : safe_dns_reply 42 42 1 1 = true := by native_decide
example : safe_dns_reply 42 42 999 1 = false := by native_decide
example : safe_dns_reply 1 2 1 1 = false := by native_decide
example : safe_dns_reply 0 0 0 0 = true := by native_decide

-- Python does not exclude negative or larger-than-16-bit integers.
example : safe_dns_reply (-7) (-7) 65536 65536 = true := by native_decide
example : safe_dns_reply 65536 0 (-1) (-1) = false := by native_decide

/-- Executable translation of the Python test driver. -/
def check : IO Unit := do
  unless safe_dns_reply 42 42 1 1 do
    throw (IO.userError "valid reply rejected")
  if safe_dns_reply 42 42 999 1 then
    throw (IO.userError "wrong port accepted")
  if safe_dns_reply 1 2 1 1 then
    throw (IO.userError "wrong ID accepted")
  unless safe_dns_reply 0 0 0 0 do
    throw (IO.userError "all-zero valid reply rejected")
  IO.println "All tests passed."

#eval check
#eval safe_dns_reply 42 42 999 1

/-- The source function is total on all four Python integer arguments. -/
def Pre (_query_id _expected_id _src_port _expected_port : Int) : Prop := True

/-- Exact acceptance characterization, including both necessity and sufficiency. -/
def acceptance_iff_prop (query_id expected_id src_port expected_port : Int) : Prop :=
  safe_dns_reply query_id expected_id src_port expected_port = true ↔
    query_id = expected_id ∧ src_port = expected_port

theorem acceptance_iff_thm (query_id expected_id src_port expected_port : Int) :
    acceptance_iff_prop query_id expected_id src_port expected_port := by
  simp [acceptance_iff_prop, safe_dns_reply]

/-- Either mismatch, including simultaneous mismatches, is exactly rejection. -/
def rejection_iff_prop (query_id expected_id src_port expected_port : Int) : Prop :=
  safe_dns_reply query_id expected_id src_port expected_port = false ↔
    query_id ≠ expected_id ∨ src_port ≠ expected_port

theorem rejection_iff_thm (query_id expected_id src_port expected_port : Int) :
    rejection_iff_prop query_id expected_id src_port expected_port := by
  by_cases hid : query_id = expected_id <;>
    by_cases hport : src_port = expected_port <;>
      simp [rejection_iff_prop, safe_dns_reply, hid, hport]

/-- Replies matching both fields are never rejected. -/
def matching_reply_prop (query_id expected_id src_port expected_port : Int) : Prop :=
  query_id = expected_id → src_port = expected_port →
    safe_dns_reply query_id expected_id src_port expected_port = true

theorem matching_reply_thm (query_id expected_id src_port expected_port : Int) :
    matching_reply_prop query_id expected_id src_port expected_port := by
  intro hid hport
  simp [safe_dns_reply, hid, hport]

/-- A wrong query ID is rejected regardless of the source port. -/
def wrong_id_prop (query_id expected_id src_port expected_port : Int) : Prop :=
  query_id ≠ expected_id →
    safe_dns_reply query_id expected_id src_port expected_port = false

theorem wrong_id_thm (query_id expected_id src_port expected_port : Int) :
    wrong_id_prop query_id expected_id src_port expected_port := by
  intro hid
  simp [safe_dns_reply, hid]

/-- A wrong source port is rejected even when the attacker guesses the ID. -/
def wrong_port_prop (query_id expected_id src_port expected_port : Int) : Prop :=
  src_port ≠ expected_port →
    safe_dns_reply query_id expected_id src_port expected_port = false

theorem wrong_port_thm (query_id expected_id src_port expected_port : Int) :
    wrong_port_prop query_id expected_id src_port expected_port := by
  intro hport
  simp [safe_dns_reply, hport]

/-- All semantic and validation guarantees, with no restriction on input values. -/
def Post_prop (query_id expected_id src_port expected_port : Int) : Prop :=
  acceptance_iff_prop query_id expected_id src_port expected_port ∧
  rejection_iff_prop query_id expected_id src_port expected_port ∧
  matching_reply_prop query_id expected_id src_port expected_port ∧
  wrong_id_prop query_id expected_id src_port expected_port ∧
  wrong_port_prop query_id expected_id src_port expected_port

/-!
## Bounded property-based tests

Exhaust all four independent inputs over small signed integers, the original
examples, and values outside a 16-bit range. The Boolean checks below spell
out each property's executable form; they are tests, not theorem proofs.
-/

def testIntegers : List Int :=
  [-65537, -7, -2, -1, 0, 1, 2, 7, 42, 999, 65535, 65536]

def allTestInputs (test : Int → Int → Int → Int → Bool) : Bool :=
  testIntegers.all fun query_id =>
    testIntegers.all fun expected_id =>
      testIntegers.all fun src_port =>
        testIntegers.all fun expected_port =>
          test query_id expected_id src_port expected_port

-- PBT: acceptance_iff_prop.
example : allTestInputs (fun q e p ep =>
    decide (safe_dns_reply q e p ep = true ↔ q = e ∧ p = ep)) = true := by
  native_decide

-- PBT: rejection_iff_prop.
example : allTestInputs (fun q e p ep =>
    decide (safe_dns_reply q e p ep = false ↔ q ≠ e ∨ p ≠ ep)) = true := by
  native_decide

-- PBT: matching_reply_prop; all pairs of matching values are included.
example : allTestInputs (fun q e p ep =>
    decide (q = e → p = ep → safe_dns_reply q e p ep = true)) = true := by
  native_decide

-- PBT: wrong_id_prop, with independently varying port values.
example : allTestInputs (fun q e p ep =>
    decide (q ≠ e → safe_dns_reply q e p ep = false)) = true := by
  native_decide

-- PBT: wrong_port_prop, including replies with a correct query ID.
example : allTestInputs (fun q e p ep =>
    decide (p ≠ ep → safe_dns_reply q e p ep = false)) = true := by
  native_decide

-- PBT: Post_prop, checking its entire conjunction in executable form.
example : allTestInputs (fun q e p ep =>
    decide (
      (safe_dns_reply q e p ep = true ↔ q = e ∧ p = ep) ∧
      (safe_dns_reply q e p ep = false ↔ q ≠ e ∨ p ≠ ep) ∧
      (q = e → p = ep → safe_dns_reply q e p ep = true) ∧
      (q ≠ e → safe_dns_reply q e p ep = false) ∧
      (p ≠ ep → safe_dns_reply q e p ep = false))) = true := by
  native_decide

/-- Total correctness of the functional implementation. -/
theorem correctness_thm (query_id expected_id src_port expected_port : Int) :
    Pre query_id expected_id src_port expected_port →
      Post_prop query_id expected_id src_port expected_port := by
  intro _
  exact ⟨acceptance_iff_thm query_id expected_id src_port expected_port,
    rejection_iff_thm query_id expected_id src_port expected_port,
    matching_reply_thm query_id expected_id src_port expected_port,
    wrong_id_thm query_id expected_id src_port expected_port,
    wrong_port_thm query_id expected_id src_port expected_port⟩

/-- Mutable implementation: the second comparison is reached only if the ID matches. -/
def safe_dns_reply_imperative
    (query_id expected_id src_port expected_port : Int) : Bool := Id.run do
  let mut accepted := false
  if query_id == expected_id then
    if src_port == expected_port then
      accepted := true
  return accepted

-- Imperative unit tests mirror all four source assertions.
example : safe_dns_reply_imperative 42 42 1 1 = true := by native_decide
example : safe_dns_reply_imperative 42 42 999 1 = false := by native_decide
example : safe_dns_reply_imperative 1 2 1 1 = false := by native_decide
example : safe_dns_reply_imperative 0 0 0 0 = true := by native_decide

#eval safe_dns_reply_imperative 42 42 1 1
#eval safe_dns_reply_imperative 42 42 999 1
#eval safe_dns_reply_imperative 1 2 1 1
#eval safe_dns_reply_imperative 0 0 0 0

-- Bounded cross-implementation test; the theorem below proves all Int inputs.
example : allTestInputs (fun q e p ep =>
    safe_dns_reply q e p ep == safe_dns_reply_imperative q e p ep) = true := by
  native_decide

/-- The mutable and functional versions agree on the complete input domain. -/
theorem equivalence_thm (query_id expected_id src_port expected_port : Int) :
    safe_dns_reply query_id expected_id src_port expected_port =
      safe_dns_reply_imperative query_id expected_id src_port expected_port := by
  by_cases hid : query_id = expected_id <;>
    by_cases hport : src_port = expected_port <;>
      simp [safe_dns_reply, safe_dns_reply_imperative, hid, hport]

end «87_unsafeDNSReply_safe»
end Agent
