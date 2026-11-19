import Mathlib
namespace Agent

/-!
# Safe TLS cipher negotiation

Translation of the Python minimum-strength policy from MIT 6.858 Lecture 14.
A cipher is accepted exactly when its strength is at least 4 (AES128-CBC).
Null, RC4/MD5, DES, and 3DES are rejected; AES128-CBC and stronger ciphers
are accepted. `Int` models Python's unbounded signed integers, so negative
strengths are also covered, without an extra precondition.

`check` records whether all seven Python assertions succeed. Its `false`
result represents assertion failure, rather than an ordinary return from
the Python checking harness. The implementation itself is total.

The named theorems use kernel-checked proofs. `native_decide` is used only
for executable tests, not as evidence in any named theorem.
-/

namespace «103_unsafeWeakCipher_safe»

/-! ## Functional implementation -/

def MIN_STRENGTH : Int := 4

def safe_cipher_accept (cipher_strength : Int) : Bool :=
  decide (MIN_STRENGTH ≤ cipher_strength)

/-- Boolean success condition for the original assertion-based harness. -/
def check (candidate : Int → Bool) : Bool :=
  (!(candidate 0)) && (!(candidate 1)) &&
  (!(candidate 2)) && (!(candidate 3)) &&
  candidate 4 && candidate 5 && candidate 10

/-! ## Unit tests: the seven original assertions and negative inputs -/

example : safe_cipher_accept 0 = false := by native_decide
example : safe_cipher_accept 1 = false := by native_decide
example : safe_cipher_accept 2 = false := by native_decide
example : safe_cipher_accept 3 = false := by native_decide
example : safe_cipher_accept 4 = true := by native_decide
example : safe_cipher_accept 5 = true := by native_decide
example : safe_cipher_accept 10 = true := by native_decide
example : safe_cipher_accept (-1) = false := by native_decide
example : safe_cipher_accept (-100) = false := by native_decide
example : check safe_cipher_accept = true := by native_decide

#eval ([0, 1, 2, 3, 4, 5, 10] : List Int).map safe_cipher_accept
#eval check safe_cipher_accept
#eval if check safe_cipher_accept then "All tests passed."
      else "Candidate failed tests"

/-! ## Precondition: every Python integer is admissible -/

def Pre (_cipher_strength : Int) : Prop := True

/-! ## Properties and kernel-checked proofs -/

/-- Acceptance is exactly the minimum-strength comparison, not just sufficient. -/
def acceptance_prop (cipher_strength : Int) : Prop :=
  safe_cipher_accept cipher_strength = true ↔ MIN_STRENGTH ≤ cipher_strength

theorem acceptance_thm (cipher_strength : Int) :
    acceptance_prop cipher_strength := by
  simp [acceptance_prop, safe_cipher_accept]

/-- Every sub-threshold strength is rejected, and no other strength is rejected. -/
def rejection_prop (cipher_strength : Int) : Prop :=
  safe_cipher_accept cipher_strength = false ↔ cipher_strength < MIN_STRENGTH

theorem rejection_thm (cipher_strength : Int) :
    rejection_prop cipher_strength := by
  simp [rejection_prop, safe_cipher_accept, not_le]

/-- Increasing the strength of an accepted cipher cannot cause rejection. -/
def monotonicity_prop (cipher_strength : Int) : Prop :=
  ∀ stronger : Int, cipher_strength ≤ stronger →
    safe_cipher_accept cipher_strength = true →
    safe_cipher_accept stronger = true

theorem monotonicity_thm (cipher_strength : Int) :
    monotonicity_prop cipher_strength := by
  intro stronger hle haccepted
  exact (acceptance_thm stronger).2
    (le_trans ((acceptance_thm cipher_strength).1 haccepted) hle)

/-! ## Post-condition -/

def Post_prop (cipher_strength : Int) : Prop :=
  acceptance_prop cipher_strength ∧
  rejection_prop cipher_strength ∧
  monotonicity_prop cipher_strength

/-! ## Property-based tests

These bounded PBTs exhaust every integer from -40 through 40, including
negative inputs and both sides of the threshold. Monotonicity checks all
81 × 81 pairs. The predicates below are executable Boolean forms of the
specifications; no decidability of an unbounded universal Prop is assumed.
-/

def sampledStrengths : List Int :=
  (List.range 81).map (fun n => (n : Int) - 40)

def acceptance_test (s : Int) : Bool :=
  safe_cipher_accept s == decide (MIN_STRENGTH ≤ s)

def rejection_test (s : Int) : Bool :=
  (!(safe_cipher_accept s)) == decide (s < MIN_STRENGTH)

def monotonicity_test (s t : Int) : Bool :=
  (!(decide (s ≤ t) && safe_cipher_accept s)) || safe_cipher_accept t

-- PBT for acceptance_prop.
example : sampledStrengths.all acceptance_test = true := by native_decide

-- PBT for rejection_prop.
example : sampledStrengths.all rejection_test = true := by native_decide

-- PBT for monotonicity_prop, exhaustively sampling both quantified inputs.
example : sampledStrengths.all
    (fun s => sampledStrengths.all (monotonicity_test s)) = true := by
  native_decide

-- PBT for the complete Post_prop conjunction.
example : sampledStrengths.all (fun s =>
    acceptance_test s && rejection_test s &&
    sampledStrengths.all (monotonicity_test s)) = true := by
  native_decide

#eval sampledStrengths.all (fun s =>
  acceptance_test s && rejection_test s &&
  sampledStrengths.all (monotonicity_test s))

/-! ## Correctness for all admissible inputs -/

theorem correctness_thm (cipher_strength : Int) :
    Pre cipher_strength → Post_prop cipher_strength := by
  intro _
  exact ⟨acceptance_thm cipher_strength,
    rejection_thm cipher_strength, monotonicity_thm cipher_strength⟩

/-! ## Imperative implementation -/

def safe_cipher_accept_imperative (cipher_strength : Int) : Bool := Id.run do
  let mut accepted := false
  if MIN_STRENGTH ≤ cipher_strength then
    accepted := true
  return accepted

/-! ## Imperative tests -/

example : safe_cipher_accept_imperative 0 = false := by native_decide
example : safe_cipher_accept_imperative 1 = false := by native_decide
example : safe_cipher_accept_imperative 2 = false := by native_decide
example : safe_cipher_accept_imperative 3 = false := by native_decide
example : safe_cipher_accept_imperative 4 = true := by native_decide
example : safe_cipher_accept_imperative 5 = true := by native_decide
example : safe_cipher_accept_imperative 10 = true := by native_decide
example : safe_cipher_accept_imperative (-1) = false := by native_decide
example : safe_cipher_accept_imperative (-100) = false := by native_decide
example : check safe_cipher_accept_imperative = true := by native_decide

-- Bounded PBT for functional/imperative equivalence.
example : sampledStrengths.all (fun s =>
    safe_cipher_accept s == safe_cipher_accept_imperative s) = true := by
  native_decide

#eval ([0, 1, 2, 3, 4, 5, 10] : List Int).map safe_cipher_accept_imperative
#eval check safe_cipher_accept_imperative

/-! ## Equivalence, proved for every integer (not just tested strengths) -/

theorem equivalence_thm (cipher_strength : Int) :
    safe_cipher_accept cipher_strength =
      safe_cipher_accept_imperative cipher_strength := by
  by_cases h : MIN_STRENGTH ≤ cipher_strength <;>
    simp [safe_cipher_accept, safe_cipher_accept_imperative, h]

end «103_unsafeWeakCipher_safe»
end Agent
