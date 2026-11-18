import Mathlib
namespace Agent

/-!
# Unsafe DNS spoofing check

Translation of the Python `unsafe_dns_check` and its test driver.
The function deliberately accepts every response without comparing transaction
IDs. This models the vulnerability, not a repaired DNS implementation.

Python integers are represented by `Int`. Although DNS transaction IDs normally
have 16 bits, the Python function imposes no range restriction; neither does
this formalization. The specifications cover negative and arbitrarily large
integers as well as ordinary DNS IDs.
-/

namespace UnsafeDNSSpoofing

/-! ## Functional implementation -/

/-- Accept a response without examining either transaction ID. -/
def unsafe_dns_check (_query_id _response_id : Int) : Bool :=
  true

/-- The three assertions and success message from the Python test driver. -/
def check : IO Unit := do
  if unsafe_dns_check 42 42 != true then
    throw (IO.userError "matching IDs rejected")
  if unsafe_dns_check 42 99 != true then
    throw (IO.userError "vuln: mismatched IDs accepted")
  if unsafe_dns_check 0 1 != true then
    throw (IO.userError "vuln: 0 vs 1 accepted")
  IO.println "All tests passed."

/-! ## Unit tests -/

example : unsafe_dns_check 42 42 = true := by native_decide
example : unsafe_dns_check 42 99 = true := by native_decide
example : unsafe_dns_check 0 1 = true := by native_decide
example : unsafe_dns_check (-1) 65536 = true := by native_decide

#eval unsafe_dns_check 42 42
#eval unsafe_dns_check 42 99
#eval unsafe_dns_check 0 1
#eval check

/-! ## Preconditions and behavioral properties -/

/-- All integer pairs are admissible, just as in the Python implementation. -/
def Pre (_query_id _response_id : Int) : Prop := True

/-- The result is always the Boolean `true`. -/
def always_accepts_prop (query_id response_id : Int) : Prop :=
  unsafe_dns_check query_id response_id = true

theorem always_accepts_thm (query_id response_id : Int) :
    always_accepts_prop query_id response_id := by
  rfl

/-- Matching IDs are accepted. -/
def matching_ids_prop (query_id : Int) : Prop :=
  unsafe_dns_check query_id query_id = true

theorem matching_ids_thm (query_id : Int) : matching_ids_prop query_id := by
  rfl

/-- The vulnerability: even a mismatched response ID is accepted. -/
def mismatched_ids_prop (query_id response_id : Int) : Prop :=
  query_id ≠ response_id → unsafe_dns_check query_id response_id = true

theorem mismatched_ids_thm (query_id response_id : Int) :
    mismatched_ids_prop query_id response_id := by
  intro _
  rfl

/-- Changing either or both inputs cannot change the decision. -/
def ids_irrelevant_prop
    (query_id response_id other_query_id other_response_id : Int) : Prop :=
  unsafe_dns_check query_id response_id =
    unsafe_dns_check other_query_id other_response_id

theorem ids_irrelevant_thm
    (query_id response_id other_query_id other_response_id : Int) :
    ids_irrelevant_prop query_id response_id other_query_id other_response_id := by
  rfl

/-! ## Postcondition -/

/-- All guarantees describe the unsafe behavior rather than DNS security. -/
def Post_prop (query_id response_id : Int) : Prop :=
  always_accepts_prop query_id response_id ∧
  matching_ids_prop query_id ∧
  mismatched_ids_prop query_id response_id ∧
  (∀ other_query_id other_response_id : Int,
    ids_irrelevant_prop query_id response_id other_query_id other_response_id)

/-! ## Property-based tests

These tests exercise executable expressions, independently of the proofs above.
The last randomized test moves the postcondition's two inner universal binders
outward, so all four IDs can be sampled. This is logically the same universally
quantified postcondition, without needing a decision procedure for a universal
proposition stored inside `Post_prop`.
-/

-- PBT for always_accepts_prop.
#eval Plausible.Testable.check
  (∀ query_id response_id : Int,
    unsafe_dns_check query_id response_id = true)

-- PBT for matching_ids_prop (generate matching pairs directly).
#eval Plausible.Testable.check
  (∀ query_id : Int, unsafe_dns_check query_id query_id = true)

-- PBT for mismatched_ids_prop. Encode the implication as a Boolean
-- disjunction to check every generated pair rather than discard equal IDs.
#eval Plausible.Testable.check
  (∀ query_id response_id : Int,
    ((query_id == response_id) || unsafe_dns_check query_id response_id) = true)

-- PBT for ids_irrelevant_prop.
#eval Plausible.Testable.check
  (∀ query_id response_id other_query_id other_response_id : Int,
    unsafe_dns_check query_id response_id =
      unsafe_dns_check other_query_id other_response_id)

-- PBT for Post_prop, with its universal binders exposed to the sampler.
#eval Plausible.Testable.check
  (∀ query_id response_id other_query_id other_response_id : Int,
    unsafe_dns_check query_id response_id = true ∧
    unsafe_dns_check query_id query_id = true ∧
    ((query_id == response_id) || unsafe_dns_check query_id response_id) = true ∧
    unsafe_dns_check query_id response_id =
      unsafe_dns_check other_query_id other_response_id)

-- Additional exhaustive mismatch testing on [-20, 20], including negative IDs.
example :
    (List.range 41).all (fun q =>
      (List.range 41).all (fun r =>
        decide (((q : Int) - 20 ≠ (r : Int) - 20) →
          unsafe_dns_check ((q : Int) - 20) ((r : Int) - 20) = true))) = true := by
  native_decide

-- Bounded PBT for the complete Post_prop, including input independence.
-- Include negative, ordinary, 16-bit boundary, and very large Python-style IDs.
def pbt_ids : List Int :=
  (List.range 11).map (fun n => (n : Int) - 5) ++
    [-65537, 42, 99, 65535, 65536, 100000000000000000000]

example :
    pbt_ids.all (fun q =>
      pbt_ids.all (fun r =>
        pbt_ids.all (fun other_q =>
          pbt_ids.all (fun other_r =>
            (unsafe_dns_check q r == true) &&
            (unsafe_dns_check q q == true) &&
            ((q == r) || unsafe_dns_check q r) &&
            (unsafe_dns_check q r == unsafe_dns_check other_q other_r))))) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (query_id response_id : Int) :
    Pre query_id response_id → Post_prop query_id response_id := by
  intro _
  refine ⟨always_accepts_thm query_id response_id,
    matching_ids_thm query_id, mismatched_ids_thm query_id response_id, ?_⟩
  intro other_query_id other_response_id
  exact ids_irrelevant_thm query_id response_id other_query_id other_response_id

/-! ## Imperative implementation -/

/-- Mutable result state, unconditionally set to `true`; no ID comparison. -/
def unsafe_dns_check_imperative (_query_id _response_id : Int) : Bool := Id.run do
  let mut accepted : Bool := false
  accepted := true
  return accepted

/-! ## Imperative tests -/

example : unsafe_dns_check_imperative 42 42 = true := by native_decide
example : unsafe_dns_check_imperative 42 99 = true := by native_decide
example : unsafe_dns_check_imperative 0 1 = true := by native_decide
example : unsafe_dns_check_imperative (-1) 65536 = true := by native_decide

#eval unsafe_dns_check_imperative 42 42
#eval unsafe_dns_check_imperative 42 99
#eval unsafe_dns_check_imperative 0 1

#eval Plausible.Testable.check
  (∀ query_id response_id : Int,
    unsafe_dns_check query_id response_id =
      unsafe_dns_check_imperative query_id response_id)

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equivalence_thm (query_id response_id : Int) :
    unsafe_dns_check query_id response_id =
      unsafe_dns_check_imperative query_id response_id := by
  rfl

end UnsafeDNSSpoofing
end Agent
