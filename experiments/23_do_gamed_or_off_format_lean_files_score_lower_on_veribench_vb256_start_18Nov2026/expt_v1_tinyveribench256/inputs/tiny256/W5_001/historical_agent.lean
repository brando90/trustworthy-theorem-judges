import Mathlib
namespace Agent

/-!
# Unsafe TLS cipher negotiation

A translation of the Python `unsafe_cipher_accept` example. Strengths are
modelled by `Int`, preserving Python's unbounded signed integer domain:
0 = null, 1 = RC4/MD5, 2 = DES, 3 = 3DES, 4 = AES128-CBC, 5 = AES256-GCM.
The implementation deliberately does not enforce a minimum strength. Its
acceptance of weak ciphers is the vulnerability being specified, not a safety
claim. Negative and unrecognised strengths are also accepted.

`check` is the executable Boolean conjunction of the Python harness's
assertions: true means that every assertion succeeds. Kernel-checked proofs
are kept separate from native unit tests and property-based tests.
-/

namespace UnsafeWeakCipher

/-! ## Functional implementation -/

/-- Intentionally unsafe: ignore the strength and accept the cipher. -/
def unsafe_cipher_accept (_cipher_strength : Int) : Bool :=
  true

/-- The assertion conditions in the original Python `check` function. -/
def check (candidate : Int → Bool) : Bool :=
  candidate 0 && candidate 1 && candidate 2 &&
    candidate 4 && candidate 5 && candidate 999

/-! ## Unit tests and the original harness -/

example : unsafe_cipher_accept 0 = true := by native_decide
example : unsafe_cipher_accept 1 = true := by native_decide
example : unsafe_cipher_accept 2 = true := by native_decide
example : unsafe_cipher_accept 4 = true := by native_decide
example : unsafe_cipher_accept 5 = true := by native_decide
example : unsafe_cipher_accept 999 = true := by native_decide
example : unsafe_cipher_accept 3 = true := by native_decide
example : unsafe_cipher_accept (-1) = true := by native_decide
example : check unsafe_cipher_accept = true := by native_decide

#eval ([0, 1, 2, 4, 5, 999] : List Int).map unsafe_cipher_accept
#eval check unsafe_cipher_accept
#eval if check unsafe_cipher_accept then "All tests passed." else "Candidate failed tests"

/-! ## Preconditions and proved properties -/

/-- Every signed integer is admissible; no cipher-strength validation occurs. -/
def Pre (_cipher_strength : Int) : Prop := True

/-- Acceptance is unconditional, including negative and unknown strengths. -/
def accepts_any_strength_prop (cipher_strength : Int) : Prop :=
  unsafe_cipher_accept cipher_strength = true

theorem accepts_any_strength_thm (cipher_strength : Int) :
    accepts_any_strength_prop cipher_strength := by
  rfl

/-- All named weak ciphers, including null and RC4/MD5, are accepted. -/
def weak_cipher_prop (cipher_strength : Int) : Prop :=
  (0 ≤ cipher_strength ∧ cipher_strength < 4) →
    unsafe_cipher_accept cipher_strength = true

theorem weak_cipher_thm (cipher_strength : Int) :
    weak_cipher_prop cipher_strength := by
  intro _
  rfl

/-- Strengths at or above the intended security threshold are also accepted. -/
def strong_cipher_prop (cipher_strength : Int) : Prop :=
  4 ≤ cipher_strength → unsafe_cipher_accept cipher_strength = true

theorem strong_cipher_thm (cipher_strength : Int) :
    strong_cipher_prop cipher_strength := by
  intro _
  rfl

/-- Changing the negotiated strength never changes the acceptance decision. -/
def strength_independent_prop (first second : Int) : Prop :=
  unsafe_cipher_accept first = unsafe_cipher_accept second

theorem strength_independent_thm (first second : Int) :
    strength_independent_prop first second := by
  rfl

/-- In particular, all six assertions in the original harness succeed. -/
theorem check_thm : check unsafe_cipher_accept = true := by
  rfl

/-! ## Postcondition -/

/-- The behavioral properties and the original Python regression checks. -/
def Post_prop (cipher_strength : Int) : Prop :=
  accepts_any_strength_prop cipher_strength ∧
  weak_cipher_prop cipher_strength ∧
  strong_cipher_prop cipher_strength ∧
  (∀ other : Int, strength_independent_prop cipher_strength other) ∧
  check unsafe_cipher_accept = true

/-! ## Property-based tests

These check executable forms rather than requiring decidability of quantified
specifications. The bounded domain includes every integer from -128 to 128,
the Python harness's large example 999, and its negative counterpart. In
particular, conditional weak-cipher tests are not left to rare random samples.
-/

def pbtStrengths : List Int :=
  (List.range 257).map (fun n => (n : Int) - 128) ++ [999, -999]

-- PBT for accepts_any_strength_prop, over all bounded strengths and random Ints.
example : pbtStrengths.all (fun s => unsafe_cipher_accept s) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ s : Int, unsafe_cipher_accept s = true)

-- PBT for weak_cipher_prop; the bound exhausts the entire weak-cipher range.
example : pbtStrengths.all (fun s =>
    decide ((0 ≤ s ∧ s < 4) → unsafe_cipher_accept s = true)) = true := by
  native_decide

-- PBT for strong_cipher_prop, including 4, 5, and 999.
example : pbtStrengths.all (fun s =>
    decide (4 ≤ s → unsafe_cipher_accept s = true)) = true := by
  native_decide

-- PBT for strength_independent_prop, checking every pair in the bounded domain.
example : pbtStrengths.all (fun first =>
    pbtStrengths.all (fun second =>
      decide (unsafe_cipher_accept first = unsafe_cipher_accept second))) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ first second : Int,
    unsafe_cipher_accept first = unsafe_cipher_accept second)

-- PBT for Post_prop: executable conjunction, with bounded comparison inputs.
example : pbtStrengths.all (fun s =>
    unsafe_cipher_accept s &&
    decide ((0 ≤ s ∧ s < 4) → unsafe_cipher_accept s = true) &&
    decide (4 ≤ s → unsafe_cipher_accept s = true) &&
    pbtStrengths.all (fun other =>
      decide (unsafe_cipher_accept s = unsafe_cipher_accept other)) &&
    check unsafe_cipher_accept) = true := by
  native_decide

-- Randomized Post_prop test: the universally quantified comparison input is
-- sampled alongside the primary input; Pre imposes no input restriction.
#eval Plausible.Testable.check
  (∀ s other : Int,
    (unsafe_cipher_accept s &&
      decide ((0 ≤ s ∧ s < 4) → unsafe_cipher_accept s = true) &&
      decide (4 ≤ s → unsafe_cipher_accept s = true) &&
      decide (unsafe_cipher_accept s = unsafe_cipher_accept other) &&
      check unsafe_cipher_accept) = true)

/-! ## Correctness with respect to the deliberately unsafe specification -/

theorem correctness_thm (cipher_strength : Int) :
    Pre cipher_strength → Post_prop cipher_strength := by
  intro _
  exact ⟨accepts_any_strength_thm cipher_strength,
    weak_cipher_thm cipher_strength,
    strong_cipher_thm cipher_strength,
    fun other => strength_independent_thm cipher_strength other,
    check_thm⟩

/-! ## Imperative implementation -/

/-- An explicit mutable decision, unconditionally set to true. -/
def unsafe_cipher_accept_imperative (_cipher_strength : Int) : Bool := Id.run do
  let mut accepted := false
  accepted := true
  return accepted

/-! ## Imperative tests -/

example : unsafe_cipher_accept_imperative 0 = true := by native_decide
example : unsafe_cipher_accept_imperative 1 = true := by native_decide
example : unsafe_cipher_accept_imperative 2 = true := by native_decide
example : unsafe_cipher_accept_imperative 4 = true := by native_decide
example : unsafe_cipher_accept_imperative 5 = true := by native_decide
example : unsafe_cipher_accept_imperative 999 = true := by native_decide
example : unsafe_cipher_accept_imperative (-1) = true := by native_decide
example : check unsafe_cipher_accept_imperative = true := by native_decide
example : pbtStrengths.all (fun s =>
    decide (unsafe_cipher_accept s = unsafe_cipher_accept_imperative s)) = true := by
  native_decide

#eval ([0, 1, 2, 4, 5, 999] : List Int).map unsafe_cipher_accept_imperative
#eval check unsafe_cipher_accept_imperative

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equiv (cipher_strength : Int) :
    unsafe_cipher_accept cipher_strength =
      unsafe_cipher_accept_imperative cipher_strength := by
  rfl

theorem functional_eq_imperative :
    unsafe_cipher_accept = unsafe_cipher_accept_imperative := by
  funext cipher_strength
  exact functional_imperative_equiv cipher_strength

end UnsafeWeakCipher
end Agent
