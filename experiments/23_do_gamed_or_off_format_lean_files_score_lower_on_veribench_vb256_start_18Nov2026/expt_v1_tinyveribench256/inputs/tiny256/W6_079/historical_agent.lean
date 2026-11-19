import Mathlib
namespace Agent

/-!
# Unsafe TCP sequence-number validation

Translation of the Python function `unsafe_tcp_seq_check` and its test driver.
Python integers are modeled by `Int`, with no sign or TCP-width restriction.
The function deliberately ignores both arguments and always returns `true`.
Thus these specifications describe the vulnerability, not a secure validator:
even a sequence number different from the expected one is accepted.

The finite executable tests are evidence only. All named theorems are proved
separately by kernel-checkable proofs for the full integer domain.
-/

namespace UnsafeTcpSeq

/-- The unsafe Python validator: neither argument is inspected. -/
def unsafe_tcp_seq_check (_seq_num _expected_seq : Int) : Bool :=
  true

-- Unit tests corresponding to the three Python assertions.
example : unsafe_tcp_seq_check 100 100 = true := by native_decide
example : unsafe_tcp_seq_check 999 100 = true := by native_decide
example : unsafe_tcp_seq_check 0 9999 = true := by native_decide

-- Python integers also include negatives and values beyond fixed TCP widths.
example : unsafe_tcp_seq_check (-1) 0 = true := by native_decide
example : unsafe_tcp_seq_check (2 ^ 100) (-(2 ^ 100)) = true := by native_decide

/-- Executable translation of the Python test driver. -/
def check : IO Unit := do
  if unsafe_tcp_seq_check 100 100 != true then
    throw (IO.userError "normal case failed")
  if unsafe_tcp_seq_check 999 100 != true then
    throw (IO.userError "vuln: wrong seq accepted")
  if unsafe_tcp_seq_check 0 9999 != true then
    throw (IO.userError "vuln: any seq accepted")
  IO.println "All tests passed."

#eval unsafe_tcp_seq_check 100 100
#eval unsafe_tcp_seq_check 999 100
#eval unsafe_tcp_seq_check 0 9999
#eval check

/-- There are no input restrictions in the Python program. -/
def Pre (_seq_num _expected_seq : Int) : Prop := True

/-- Every pair of integer arguments is accepted. -/
def always_accepts_prop (seq_num expected_seq : Int) : Prop :=
  unsafe_tcp_seq_check seq_num expected_seq = true

theorem always_accepts_thm (seq_num expected_seq : Int) :
    always_accepts_prop seq_num expected_seq := by
  rfl

/-- In particular, the normal case of equal sequence numbers is accepted. -/
def matching_seq_prop (seq_num expected_seq : Int) : Prop :=
  seq_num = expected_seq → unsafe_tcp_seq_check seq_num expected_seq = true

theorem matching_seq_thm (seq_num expected_seq : Int) :
    matching_seq_prop seq_num expected_seq := by
  intro _
  rfl

/-- The vulnerability: unequal sequence numbers are also accepted. -/
def mismatching_seq_prop (seq_num expected_seq : Int) : Prop :=
  seq_num ≠ expected_seq → unsafe_tcp_seq_check seq_num expected_seq = true

theorem mismatching_seq_thm (seq_num expected_seq : Int) :
    mismatching_seq_prop seq_num expected_seq := by
  intro _
  rfl

/-- Changing either or both arguments never changes the result. -/
def input_independent_prop (seq_num expected_seq : Int) : Prop :=
  ∀ other_seq other_expected : Int,
    unsafe_tcp_seq_check seq_num expected_seq =
      unsafe_tcp_seq_check other_seq other_expected

theorem input_independent_thm (seq_num expected_seq : Int) :
    input_independent_prop seq_num expected_seq := by
  intro other_seq other_expected
  rfl

/-- All guarantees describe actual (unsafe) behavior, not secure validation. -/
def Post_prop (seq_num expected_seq : Int) : Prop :=
  always_accepts_prop seq_num expected_seq ∧
  matching_seq_prop seq_num expected_seq ∧
  mismatching_seq_prop seq_num expected_seq ∧
  input_independent_prop seq_num expected_seq

/-! ## Bounded property-based tests

The sample domain includes every integer from -8 through 8, together with the
original regression-test inputs and large positive/negative integers. The tests
below use executable Boolean forms rather than Decidable instances for the
specification predicates. Implications are checked as `not premise or result`.
The input-independence quantifiers are exhaustively checked on the same domain.
-/

def pbtInputs : List Int :=
  (List.range 17).map (fun n => (n : Int) - 8) ++
    [100, 999, 9999, 2 ^ 100, -(2 ^ 100)]

-- PBT for always_accepts_prop.
example : pbtInputs.all (fun seq_num =>
    pbtInputs.all (fun expected_seq =>
      unsafe_tcp_seq_check seq_num expected_seq == true)) = true := by
  native_decide

-- PBT for matching_seq_prop; the domain includes all diagonal (equal) pairs.
example : pbtInputs.all (fun seq_num =>
    pbtInputs.all (fun expected_seq =>
      (!(seq_num == expected_seq)) ||
        (unsafe_tcp_seq_check seq_num expected_seq == true))) = true := by
  native_decide

-- PBT for mismatching_seq_prop; unequal pairs exercise the vulnerability.
example : pbtInputs.all (fun seq_num =>
    pbtInputs.all (fun expected_seq =>
      (seq_num == expected_seq) ||
        (unsafe_tcp_seq_check seq_num expected_seq == true))) = true := by
  native_decide

-- PBT for input_independent_prop: all four arguments vary independently.
example : pbtInputs.all (fun seq_num =>
    pbtInputs.all (fun expected_seq =>
      pbtInputs.all (fun other_seq =>
        pbtInputs.all (fun other_expected =>
          unsafe_tcp_seq_check seq_num expected_seq ==
            unsafe_tcp_seq_check other_seq other_expected)))) = true := by
  native_decide

-- PBT for the complete conjunction Post_prop.
example : pbtInputs.all (fun seq_num =>
    pbtInputs.all (fun expected_seq =>
      (unsafe_tcp_seq_check seq_num expected_seq == true) &&
      ((!(seq_num == expected_seq)) ||
        (unsafe_tcp_seq_check seq_num expected_seq == true)) &&
      ((seq_num == expected_seq) ||
        (unsafe_tcp_seq_check seq_num expected_seq == true)) &&
      pbtInputs.all (fun other_seq =>
        pbtInputs.all (fun other_expected =>
          unsafe_tcp_seq_check seq_num expected_seq ==
            unsafe_tcp_seq_check other_seq other_expected)))) = true := by
  native_decide

/-- The unrestricted precondition implies every stated postcondition. -/
theorem correctness_thm (seq_num expected_seq : Int) :
    Pre seq_num expected_seq → Post_prop seq_num expected_seq := by
  intro _
  exact ⟨always_accepts_thm seq_num expected_seq,
    matching_seq_thm seq_num expected_seq,
    mismatching_seq_thm seq_num expected_seq,
    input_independent_thm seq_num expected_seq⟩

/-- Imperative version: overwrite a mutable result with `true`, without validation. -/
def unsafe_tcp_seq_check_imp (_seq_num _expected_seq : Int) : Bool := Id.run do
  let mut accepted := false
  accepted := true
  return accepted

-- Imperative regression tests.
example : unsafe_tcp_seq_check_imp 100 100 = true := by native_decide
example : unsafe_tcp_seq_check_imp 999 100 = true := by native_decide
example : unsafe_tcp_seq_check_imp 0 9999 = true := by native_decide
example : unsafe_tcp_seq_check_imp (-1) (2 ^ 100) = true := by native_decide

#eval unsafe_tcp_seq_check_imp 100 100
#eval unsafe_tcp_seq_check_imp 999 100
#eval unsafe_tcp_seq_check_imp 0 9999

-- Bounded equivalence test, in addition to the universal proof below.
example : pbtInputs.all (fun seq_num =>
    pbtInputs.all (fun expected_seq =>
      unsafe_tcp_seq_check seq_num expected_seq ==
        unsafe_tcp_seq_check_imp seq_num expected_seq)) = true := by
  native_decide

/-- Functional and imperative implementations agree on every pair of integers. -/
theorem functional_imperative_equiv_thm (seq_num expected_seq : Int) :
    unsafe_tcp_seq_check seq_num expected_seq =
      unsafe_tcp_seq_check_imp seq_num expected_seq := by
  rfl

end UnsafeTcpSeq
end Agent
