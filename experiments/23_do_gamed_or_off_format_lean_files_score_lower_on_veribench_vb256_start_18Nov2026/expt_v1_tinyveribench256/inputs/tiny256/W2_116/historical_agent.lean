import Mathlib
namespace Agent

/-!
# Safe DNS transaction-ID validation

Translation of the Python `safe_dns_check` and its four checks. A response is
accepted exactly when its transaction ID equals the query ID. Python integers
are modeled by `Int`: the implementation does not truncate IDs to 16 bits or
reject negative integers. No additional input restriction is necessary.

The proved security condition is exact ID validation. Probabilistic claims
about guessing IDs, or broader DNS cache-poisoning defenses, would require an
additional model of the network and attacker and are not assumed here.
-/

namespace UnsafeDNSSpoofingSafe

/-! ## Functional implementation -/

def safe_dns_check (query_id response_id : Int) : Bool :=
  query_id == response_id

/-! ## Unit tests and the executable Python-style check -/

example : safe_dns_check 42 42 = true := by native_decide
example : safe_dns_check 42 99 = false := by native_decide
example : safe_dns_check 0 0 = true := by native_decide
example : safe_dns_check 0 1 = false := by native_decide

-- The Python function also works on negative and arbitrarily large integers.
example : safe_dns_check (-7) (-7) = true := by native_decide
example : safe_dns_check (-7) 7 = false := by native_decide
example : safe_dns_check 0 65536 = false := by native_decide
example : safe_dns_check 18446744073709551616 18446744073709551616 = true := by
  native_decide

def check : IO Unit := do
  unless safe_dns_check 42 42 do
    throw (IO.userError "matching IDs rejected")
  if safe_dns_check 42 99 then
    throw (IO.userError "mismatched IDs accepted")
  unless safe_dns_check 0 0 do
    throw (IO.userError "zero IDs rejected")
  if safe_dns_check 0 1 then
    throw (IO.userError "0 vs 1 accepted")
  IO.println "All tests passed."

#eval check

/-! ## Precondition and semantic properties -/

-- Every pair of Python integers is admissible.
def Pre (_query_id _response_id : Int) : Prop := True

-- Equal IDs must be accepted.
def matching_prop (query_id : Int) : Prop :=
  safe_dns_check query_id query_id = true

theorem matching_thm (query_id : Int) : matching_prop query_id := by
  simp [matching_prop, safe_dns_check]

-- Unequal IDs must be rejected.
def mismatching_prop (query_id response_id : Int) : Prop :=
  query_id ≠ response_id → safe_dns_check query_id response_id = false

theorem mismatching_thm (query_id response_id : Int) :
    mismatching_prop query_id response_id := by
  unfold mismatching_prop
  intro h
  simp [safe_dns_check, h]

-- Exact acceptance characterization: in particular, no mismatched ID is accepted.
def validation_prop (query_id response_id : Int) : Prop :=
  safe_dns_check query_id response_id = true ↔ query_id = response_id

theorem validation_thm (query_id response_id : Int) :
    validation_prop query_id response_id := by
  simp [validation_prop, safe_dns_check]

/-! ## Postcondition -/

def Post_prop (query_id response_id : Int) : Prop :=
  matching_prop query_id ∧
  mismatching_prop query_id response_id ∧
  validation_prop query_id response_id

/-! ## Bounded property-based tests

Exhaust all integers from -32 through 32, together with representative DNS IDs,
out-of-range IDs, and integers beyond a machine word. Pairwise tests exhaust
all pairs from this collection. These executable Boolean checks are evidence,
not substitutes for the universally quantified proofs.
-/

def pbtIDs : List Int :=
  (List.range 65).map (fun n => (n : Int) - 32) ++
    [42, 99, 65535, 65536, -65536,
     18446744073709551616, -18446744073709551616]

-- PBT for matching_prop.
example : pbtIDs.all (fun q => safe_dns_check q q) = true := by
  native_decide

-- PBT for mismatching_prop: q != r implies a false result.
example : pbtIDs.all (fun q => pbtIDs.all (fun r =>
    (q == r) || !(safe_dns_check q r))) = true := by
  native_decide

-- PBT for validation_prop: the result agrees exactly with equality.
example : pbtIDs.all (fun q => pbtIDs.all (fun r =>
    safe_dns_check q r == (q == r))) = true := by
  native_decide

-- PBT for the complete Post_prop, with all three conjuncts checked together.
example : pbtIDs.all (fun q => pbtIDs.all (fun r =>
    safe_dns_check q q &&
    ((q == r) || !(safe_dns_check q r)) &&
    (safe_dns_check q r == (q == r)))) = true := by
  native_decide

#eval pbtIDs.all (fun q => pbtIDs.all (fun r =>
  safe_dns_check q q &&
  ((q == r) || !(safe_dns_check q r)) &&
  (safe_dns_check q r == (q == r))))

/-! ## Correctness for every admissible pair -/

theorem correctness_thm (query_id response_id : Int) :
    Pre query_id response_id → Post_prop query_id response_id := by
  intro _
  exact ⟨matching_thm query_id,
    mismatching_thm query_id response_id,
    validation_thm query_id response_id⟩

/-! ## Imperative implementation -/

def safe_dns_check_imperative (query_id response_id : Int) : Bool := Id.run do
  let mut accepted := false
  if query_id == response_id then
    accepted := true
  return accepted

/-! ## Imperative tests -/

example : safe_dns_check_imperative 42 42 = true := by native_decide
example : safe_dns_check_imperative 42 99 = false := by native_decide
example : safe_dns_check_imperative 0 0 = true := by native_decide
example : safe_dns_check_imperative 0 1 = false := by native_decide
example : safe_dns_check_imperative (-7) (-7) = true := by native_decide
example : safe_dns_check_imperative 0 65536 = false := by native_decide

#eval [safe_dns_check_imperative 42 42, safe_dns_check_imperative 42 99,
  safe_dns_check_imperative 0 0, safe_dns_check_imperative 0 1]

example : pbtIDs.all (fun q => pbtIDs.all (fun r =>
    safe_dns_check q r == safe_dns_check_imperative q r)) = true := by
  native_decide

/-! ## Functional / imperative equivalence -/

theorem functional_eq_imperative_thm (query_id response_id : Int) :
    safe_dns_check query_id response_id =
      safe_dns_check_imperative query_id response_id := by
  by_cases h : query_id = response_id <;>
    simp [safe_dns_check, safe_dns_check_imperative, h]

end UnsafeDNSSpoofingSafe
end Agent
