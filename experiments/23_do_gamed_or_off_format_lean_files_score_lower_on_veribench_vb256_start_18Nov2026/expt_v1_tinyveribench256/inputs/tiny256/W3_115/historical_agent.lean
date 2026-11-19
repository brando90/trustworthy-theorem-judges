import Mathlib
namespace Agent

/-!
# Safe TCP sequence-number validation

Translation of the Python exact-match sequence check. Python integers are
modelled by `Int`, with no nonnegativity or fixed-width restriction. The check
accepts exactly the expected sequence number; every different number is rejected.
This formalizes the validation rule, not a probabilistic or network-level claim
about an attacker's knowledge. The functional and mutable implementations are
proved equivalent on the entire integer domain.
-/

namespace «44_unsafeTcpSeq_safe»

/-- Return true exactly when the supplied sequence number equals the expected one. -/
def safe_tcp_seq_check (seq_num expected_seq : Int) : Bool :=
  decide (seq_num = expected_seq)

-- The three assertions from the Python `check` function.
example : safe_tcp_seq_check 100 100 = true := by native_decide
example : safe_tcp_seq_check 999 100 = false := by native_decide
example : safe_tcp_seq_check 0 1 = false := by native_decide

-- Negative values and zero are also legitimate Python integer inputs.
example : safe_tcp_seq_check (-7) (-7) = true := by native_decide
example : safe_tcp_seq_check (-7) 7 = false := by native_decide
example : safe_tcp_seq_check 0 0 = true := by native_decide

#eval safe_tcp_seq_check 100 100
#eval safe_tcp_seq_check 999 100
#eval safe_tcp_seq_check 0 1
#eval if safe_tcp_seq_check 100 100 &&
    !(safe_tcp_seq_check 999 100) && !(safe_tcp_seq_check 0 1)
  then "All tests passed." else "A test failed."

/-- There are no restrictions on the two Python integer arguments. -/
def Pre (_seq_num _expected_seq : Int) : Prop := True

/-- Acceptance is equivalent to exact equality, not a window or partial match. -/
def exact_match_prop (seq_num expected_seq : Int) : Prop :=
  safe_tcp_seq_check seq_num expected_seq = true ↔ seq_num = expected_seq

theorem exact_match_thm (seq_num expected_seq : Int) :
    exact_match_prop seq_num expected_seq := by
  simp [exact_match_prop, safe_tcp_seq_check]

/-- A matching sequence number is never rejected. -/
def valid_seq_prop (seq_num expected_seq : Int) : Prop :=
  seq_num = expected_seq → safe_tcp_seq_check seq_num expected_seq = true

theorem valid_seq_thm (seq_num expected_seq : Int) :
    valid_seq_prop seq_num expected_seq := by
  intro h
  simp [safe_tcp_seq_check, h]

/-- Rejection is equivalent to inequality; in particular, no wrong number passes. -/
def invalid_seq_prop (seq_num expected_seq : Int) : Prop :=
  safe_tcp_seq_check seq_num expected_seq = false ↔ seq_num ≠ expected_seq

theorem invalid_seq_thm (seq_num expected_seq : Int) :
    invalid_seq_prop seq_num expected_seq := by
  simp [invalid_seq_prop, safe_tcp_seq_check]

/-- Complete acceptance and rejection contract for the returned Boolean. -/
def Post_prop (seq_num expected_seq : Int) : Prop :=
  exact_match_prop seq_num expected_seq ∧
  valid_seq_prop seq_num expected_seq ∧
  invalid_seq_prop seq_num expected_seq

-- Property-based tests exhaust all 4,225 pairs in [-32, 32]². These bounds
-- restrict only the tests; every theorem above and below quantifies over Int.
private def pbtInputs : List Int :=
  (List.range 65).map (fun n => (n : Int) - 32)

-- PBT for exact_match_prop: Boolean equivalence of acceptance and equality.
example : (pbtInputs.all (fun s => pbtInputs.all (fun e =>
    (safe_tcp_seq_check s e == true) == decide (s = e)))) = true := by
  native_decide

-- PBT for valid_seq_prop: executable implication, including every diagonal pair.
example : (pbtInputs.all (fun s => pbtInputs.all (fun e =>
    !(decide (s = e)) || (safe_tcp_seq_check s e == true)))) = true := by
  native_decide

-- PBT for invalid_seq_prop: Boolean equivalence of rejection and inequality.
example : (pbtInputs.all (fun s => pbtInputs.all (fun e =>
    (safe_tcp_seq_check s e == false) == decide (s ≠ e)))) = true := by
  native_decide

-- PBT for Post_prop: check the conjunction of all three executable properties.
example : (pbtInputs.all (fun s => pbtInputs.all (fun e =>
    ((safe_tcp_seq_check s e == true) == decide (s = e)) &&
    (!(decide (s = e)) || (safe_tcp_seq_check s e == true)) &&
    ((safe_tcp_seq_check s e == false) == decide (s ≠ e))))) = true := by
  native_decide

#eval pbtInputs.all (fun s => pbtInputs.all (fun e =>
  ((safe_tcp_seq_check s e == true) == decide (s = e)) &&
  (!(decide (s = e)) || (safe_tcp_seq_check s e == true)) &&
  ((safe_tcp_seq_check s e == false) == decide (s ≠ e))))

/-- The implementation satisfies the full contract for all admissible inputs. -/
theorem correctness_thm (seq_num expected_seq : Int) :
    Pre seq_num expected_seq → Post_prop seq_num expected_seq := by
  intro _
  exact ⟨exact_match_thm seq_num expected_seq,
    valid_seq_thm seq_num expected_seq, invalid_seq_thm seq_num expected_seq⟩

/-- Imperative version: start rejected and accept only upon an exact match. -/
def safe_tcp_seq_check_imp (seq_num expected_seq : Int) : Bool := Id.run do
  let mut accepted := false
  if seq_num = expected_seq then
    accepted := true
  return accepted

example : safe_tcp_seq_check_imp 100 100 = true := by native_decide
example : safe_tcp_seq_check_imp 999 100 = false := by native_decide
example : safe_tcp_seq_check_imp 0 1 = false := by native_decide
example : safe_tcp_seq_check_imp (-7) (-7) = true := by native_decide
example : safe_tcp_seq_check_imp (-7) 7 = false := by native_decide

#eval safe_tcp_seq_check_imp 100 100
#eval safe_tcp_seq_check_imp 999 100
#eval safe_tcp_seq_check_imp 0 1

-- Additional bounded cross-check of the two implementations.
example : (pbtInputs.all (fun s => pbtInputs.all (fun e =>
    safe_tcp_seq_check s e == safe_tcp_seq_check_imp s e))) = true := by
  native_decide

/-- Functional and imperative results agree for every pair of integers. -/
theorem equivalence_thm (seq_num expected_seq : Int) :
    safe_tcp_seq_check seq_num expected_seq =
      safe_tcp_seq_check_imp seq_num expected_seq := by
  by_cases h : seq_num = expected_seq <;>
    simp [safe_tcp_seq_check, safe_tcp_seq_check_imp, h]

end «44_unsafeTcpSeq_safe»
end Agent
