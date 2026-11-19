import Mathlib
namespace Agent

/-!
# Unsafe WEP keystream-reuse check

Translation of the Python `unsafe_wep_check` and its `check` harness.
The function unconditionally accepts packets: equal IVs, distinct IVs, and
zero IVs all produce `true`. This deliberately preserves the vulnerability,
not a secure IV-reuse detector. No RC4 or ciphertext operation is performed.

Python's unrestricted integer arguments are modeled by `Int`. Although WEP
normally uses 24-bit IVs, the source imposes no range restriction, so neither
does this specification. Bounded tests include negative and out-of-range IVs.
-/

namespace UnsafeWepKeystream

-- Functional implementation.
def unsafe_wep_check (_iv1 _iv2 : Int) : Bool :=
  true

-- Fixed unit tests, including all three assertions in the Python source.
example : unsafe_wep_check 5 5 = true := by native_decide
example : unsafe_wep_check 1 2 = true := by native_decide
example : unsafe_wep_check 0 0 = true := by native_decide
example : unsafe_wep_check (-7) 16777216 = true := by native_decide

#eval unsafe_wep_check 5 5
#eval unsafe_wep_check 1 2
#eval unsafe_wep_check 0 0

-- Executable counterpart of the Python assertion/printing harness.
def check : IO Unit := do
  unless unsafe_wep_check 5 5 do
    throw (IO.userError "vuln: reused IV accepted")
  unless unsafe_wep_check 1 2 do
    throw (IO.userError "distinct IVs accepted")
  unless unsafe_wep_check 0 0 do
    throw (IO.userError "vuln: zero IVs accepted")
  IO.println "All tests passed."

#eval check

-- Every pair of Python integers is admissible.
def Pre (_iv1 _iv2 : Int) : Prop := True

-- Exact return-value semantics.
def always_accepts_prop (iv1 iv2 : Int) : Prop :=
  unsafe_wep_check iv1 iv2 = true

theorem always_accepts_thm (iv1 iv2 : Int) :
    always_accepts_prop iv1 iv2 := by
  rfl

-- The unsafe behavior: IV reuse is not rejected.
def reused_iv_accepted_prop (iv1 iv2 : Int) : Prop :=
  iv1 = iv2 → unsafe_wep_check iv1 iv2 = true

theorem reused_iv_accepted_thm (iv1 iv2 : Int) :
    reused_iv_accepted_prop iv1 iv2 := by
  intro _
  rfl

-- Distinct IVs receive exactly the same acceptance result.
def distinct_ivs_accepted_prop (iv1 iv2 : Int) : Prop :=
  iv1 ≠ iv2 → unsafe_wep_check iv1 iv2 = true

theorem distinct_ivs_accepted_thm (iv1 iv2 : Int) :
    distinct_ivs_accepted_prop iv1 iv2 := by
  intro _
  rfl

-- Postcondition: exact output and both equality cases.
def Post_prop (iv1 iv2 : Int) : Prop :=
  always_accepts_prop iv1 iv2 ∧
  reused_iv_accepted_prop iv1 iv2 ∧
  distinct_ivs_accepted_prop iv1 iv2

-- Property-based tests. Each check exhausts 36 * 36 input pairs.
-- The test domain contains [-16, 16], the largest 24-bit IV, and
-- both positive and negative values outside the unsigned 24-bit range.
def testIVs : List Int :=
  (List.range 33).map (fun n => (n : Int) - 16) ++
    [16777215, 16777216, -16777216]

-- PBT for always_accepts_prop: Boolean output is true on every pair.
example : testIVs.all (fun iv1 =>
    testIVs.all (fun iv2 => unsafe_wep_check iv1 iv2)) = true := by
  native_decide

-- PBT for reused_iv_accepted_prop: (iv1 = iv2) implies acceptance.
-- Boolean implication is implemented as not-antecedent OR consequent.
example : testIVs.all (fun iv1 =>
    testIVs.all (fun iv2 =>
      decide (iv1 ≠ iv2) || unsafe_wep_check iv1 iv2)) = true := by
  native_decide

-- PBT for distinct_ivs_accepted_prop: (iv1 ≠ iv2) implies acceptance.
example : testIVs.all (fun iv1 =>
    testIVs.all (fun iv2 =>
      decide (iv1 = iv2) || unsafe_wep_check iv1 iv2)) = true := by
  native_decide

-- PBT for Post_prop, testing the conjunction's executable Boolean form.
-- Pre is True, so every tested pair is admissible.
example : testIVs.all (fun iv1 =>
    testIVs.all (fun iv2 =>
      unsafe_wep_check iv1 iv2 &&
      (decide (iv1 ≠ iv2) || unsafe_wep_check iv1 iv2) &&
      (decide (iv1 = iv2) || unsafe_wep_check iv1 iv2))) = true := by
  native_decide

-- Kernel-checked correctness, independent of the testing evidence.
theorem correctness_thm (iv1 iv2 : Int) :
    Pre iv1 iv2 → Post_prop iv1 iv2 := by
  intro _
  exact ⟨always_accepts_thm iv1 iv2,
    reused_iv_accepted_thm iv1 iv2, distinct_ivs_accepted_thm iv1 iv2⟩

-- Imperative implementation: the result is set without examining either IV.
def unsafe_wep_check_imp (_iv1 _iv2 : Int) : Bool := Id.run do
  let mut accepted := false
  accepted := true
  return accepted

-- Imperative unit tests and executable evaluations.
example : unsafe_wep_check_imp 5 5 = true := by native_decide
example : unsafe_wep_check_imp 1 2 = true := by native_decide
example : unsafe_wep_check_imp 0 0 = true := by native_decide
example : unsafe_wep_check_imp (-7) 16777216 = true := by native_decide

#eval unsafe_wep_check_imp 5 5
#eval unsafe_wep_check_imp 1 2
#eval unsafe_wep_check_imp 0 0

-- Bounded PBT for functional/imperative equivalence.
example : testIVs.all (fun iv1 =>
    testIVs.all (fun iv2 =>
      unsafe_wep_check iv1 iv2 == unsafe_wep_check_imp iv1 iv2)) = true := by
  native_decide

-- Both definitions reduce to true for every pair of integers.
theorem functional_imperative_equivalence_thm (iv1 iv2 : Int) :
    unsafe_wep_check iv1 iv2 = unsafe_wep_check_imp iv1 iv2 := by
  rfl

end UnsafeWepKeystream
end Agent
