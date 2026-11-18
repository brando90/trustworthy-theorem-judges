import Mathlib
namespace Agent

/-!
# Unsafe RSA exponentiation without blinding

This models Python's `pow(message, d, n)` on arbitrary integers. `Except`
represents the two ValueError cases: a zero modulus and a noninvertible base
with negative exponent. Negative moduli use Python's signed remainder, not
Lean's always-nonnegative Euclidean remainder. For ordinary RSA inputs the
result is simply `message ^ d % n`. No random value or blinding factor is
introduced. The absence of blinding is a functional property; this file does
not assert a machine-level timing model or prove a timing attack.
-/

namespace UnsafeRSABlinding

deriving instance DecidableEq for Except

inductive PowError where
  | zeroModulus
  | notInvertible
  deriving DecidableEq, Repr

/-- Python remainder, including its sign convention for a negative divisor. -/
def pythonMod (a n : Int) : Int :=
  if n < 0 then -((-a) % (-n)) else a % n

/-- Direct, unblinded modular exponentiation. The extended-gcd coefficient
is the inverse base when the exponent is negative. -/
def unsafe_rsa_decrypt (message d n : Int) : Except PowError Int :=
  if n = 0 then .error .zeroModulus
  else if d < 0 ∧ Int.gcd message n ≠ 1 then .error .notInvertible
  else .ok (pythonMod ((if d < 0 then Int.gcdA message n else message) ^ d.natAbs) n)

def unsafe_blinding_applied (_message _d _n : Int) : Bool := false

-- The four checks from the Python source.
example : unsafe_rsa_decrypt 2 3 35 = .ok (2 ^ 3 % 35) := by native_decide
example : unsafe_rsa_decrypt 5 7 11 = .ok (5 ^ 7 % 11) := by native_decide
example : unsafe_blinding_applied 2 3 35 = false := by native_decide
example : unsafe_blinding_applied 0 0 1 = false := by native_decide
-- Additional Python integer and exception cases.
example : unsafe_rsa_decrypt (-2) 3 35 = .ok 27 := by native_decide
example : unsafe_rsa_decrypt 2 3 (-35) = .ok (-27) := by native_decide
example : unsafe_rsa_decrypt 2 (-1) 35 = .ok 18 := by native_decide
example : unsafe_rsa_decrypt 2 (-1) (-35) = .ok (-17) := by native_decide
example : unsafe_rsa_decrypt 0 0 1 = .ok 0 := by native_decide
example : unsafe_rsa_decrypt 0 (-1) 1 = .ok 0 := by native_decide
example : unsafe_rsa_decrypt 2 3 0 = .error .zeroModulus := by native_decide
example : unsafe_rsa_decrypt 5 (-1) 35 = .error .notInvertible := by native_decide
#eval (unsafe_rsa_decrypt 2 3 35, unsafe_rsa_decrypt 5 7 11)
#eval (unsafe_blinding_applied 2 3 35, unsafe_blinding_applied 0 0 1)

/-- Exactly the inputs for which Python's three-argument pow returns normally.
The implementation still models exceptions outside this precondition. -/
def Pre (message d n : Int) : Prop :=
  n ≠ 0 ∧ (d < 0 → Int.gcd message n = 1)

instance (m d n : Int) : Decidable (Pre m d n) := by
  unfold Pre
  infer_instance

/-- Signed remainders still represent the same congruence class. -/
theorem pythonMod_mod (a n : Int) : pythonMod a n % n = a % n := by
  unfold pythonMod
  split_ifs with h
  · rw [Int.emod_neg]
    simpa using (Int.mod_modEq (-a) n).neg
  · simp

theorem pythonMod_bounds (a n : Int) (hn : n ≠ 0) :
    (0 < n → 0 ≤ pythonMod a n ∧ pythonMod a n < n) ∧
    (n < 0 → n < pythonMod a n ∧ pythonMod a n ≤ 0) := by
  constructor
  · intro hp
    simp only [pythonMod, if_neg (by omega : ¬ n < 0)]
    exact ⟨Int.emod_nonneg a hn, Int.emod_lt_of_pos a hp⟩
  · intro hm
    simp only [pythonMod, if_pos hm]
    have h₁ := Int.emod_nonneg (-a) (by omega : -n ≠ 0)
    have h₂ := Int.emod_lt_of_pos (-a) (by omega : 0 < -n)
    omega

/-- Bezout's coefficient is genuinely a multiplicative inverse modulo n. -/
theorem inverse_mod (m n : Int) (hg : Int.gcd m n = 1) :
    (Int.gcdA m n * m) % n = 1 % n := by
  apply Int.modEq_iff_dvd.mpr
  refine ⟨Int.gcdB m n, ?_⟩
  have h := Int.gcd_eq_gcd_ab m n
  rw [hg] at h
  norm_num at h
  nlinarith

/-- Exact ordinary exponentiation, with no blinding multiplier. -/
def direct_power_prop (m d n : Int) : Prop :=
  0 ≤ d → n ≠ 0 →
    unsafe_rsa_decrypt m d n = .ok (pythonMod (m ^ d.toNat) n)

theorem direct_power_thm (m d n : Int) : direct_power_prop m d n := by
  intro hd hn
  have hnot : ¬ d < 0 := by omega
  have habs : d.natAbs = d.toNat := by omega
  simp [unsafe_rsa_decrypt, hn, hnot, habs]

/-- For positive exponents the answer is congruent to the power. For negative
exponents it is the inverse of the corresponding positive power. -/
def arithmetic_prop (m d n : Int) : Prop :=
  match unsafe_rsa_decrypt m d n with
  | .error _ => True
  | .ok r => if 0 ≤ d then r % n = m ^ d.natAbs % n
      else (r * m ^ d.natAbs) % n = 1 % n

theorem arithmetic_thm (m d n : Int) : arithmetic_prop m d n := by
  unfold arithmetic_prop unsafe_rsa_decrypt
  by_cases hn : n = 0
  · simp [hn]
  by_cases hb : d < 0 ∧ Int.gcd m n ≠ 1
  · simp [hn, hb]
  simp only [if_neg hn, if_neg hb]
  by_cases hd : 0 ≤ d
  · have hnot : ¬ d < 0 := by omega
    simp [hd, hnot, pythonMod_mod]
  · have hneg : d < 0 := by omega
    have hg : Int.gcd m n = 1 := by tauto
    simp only [if_neg hd, if_pos hneg]
    have hi : Int.ModEq n (Int.gcdA m n * m) 1 := inverse_mod m n hg
    have hp := hi.pow d.natAbs
    have hr : Int.ModEq n
        (pythonMod (Int.gcdA m n ^ d.natAbs) n)
        (Int.gcdA m n ^ d.natAbs) := pythonMod_mod _ _
    have hc := hr.mul (Int.ModEq.refl (m ^ d.natAbs))
    exact hc.trans (by simpa [mul_pow] using hp)

/-- Python's canonical representative has the sign of the modulus. -/
def range_prop (m d n : Int) : Prop :=
  match unsafe_rsa_decrypt m d n with
  | .error _ => True
  | .ok r => if 0 < n then 0 ≤ r ∧ r < n else n < r ∧ r ≤ 0

theorem range_thm (m d n : Int) : range_prop m d n := by
  unfold range_prop unsafe_rsa_decrypt
  by_cases hn : n = 0
  · simp [hn]
  by_cases hb : d < 0 ∧ Int.gcd m n ≠ 1
  · simp [hn, hb]
  simp only [if_neg hn, if_neg hb]
  have h := pythonMod_bounds
    ((if d < 0 then Int.gcdA m n else m) ^ d.natAbs) n hn
  by_cases hp : 0 < n
  · simpa only [if_pos hp] using h.1 hp
  · simpa only [if_neg hp] using h.2 (by omega : n < 0)

/-- The advertised vulnerability: no input ever enables blinding. -/
def no_blinding_prop (m d n : Int) : Prop :=
  unsafe_blinding_applied m d n = false

theorem no_blinding_thm (m d n : Int) : no_blinding_prop m d n := by
  rfl

/-- Both exceptional outcomes are characterized exactly, including priority
of the zero-modulus check. -/
def errors_prop (m d n : Int) : Prop :=
  (unsafe_rsa_decrypt m d n = .error .zeroModulus ↔ n = 0) ∧
  (unsafe_rsa_decrypt m d n = .error .notInvertible ↔
    n ≠ 0 ∧ d < 0 ∧ Int.gcd m n ≠ 1)

theorem errors_thm (m d n : Int) : errors_prop m d n := by
  unfold errors_prop unsafe_rsa_decrypt
  by_cases hn : n = 0 <;>
    by_cases hb : d < 0 ∧ Int.gcd m n ≠ 1 <;>
      simp only [hn, hb, if_true, if_false] <;> simp_all

/-- This precondition is necessary as well as sufficient for a normal return. -/
def success_prop (m d n : Int) : Prop :=
  (match unsafe_rsa_decrypt m d n with
    | .ok _ => True
    | .error _ => False) ↔ Pre m d n

theorem success_thm (m d n : Int) : success_prop m d n := by
  unfold success_prop unsafe_rsa_decrypt Pre
  by_cases hn : n = 0 <;>
    by_cases hb : d < 0 ∧ Int.gcd m n ≠ 1 <;>
      simp only [hn, hb, if_true, if_false] <;> simp_all

/-- The postcondition combines arithmetic, representation, error behavior,
and the fact that this is the unsafe (unblinded) implementation. -/
def Post_prop (m d n : Int) : Prop :=
  direct_power_prop m d n ∧ arithmetic_prop m d n ∧ range_prop m d n ∧
  no_blinding_prop m d n ∧ errors_prop m d n ∧ success_prop m d n

-- Executable decisions for the specifications; no classical decision oracle
-- is used by the property-based tests.
instance (m d n : Int) : Decidable (direct_power_prop m d n) := by
  unfold direct_power_prop
  infer_instance
instance (m d n : Int) : Decidable (arithmetic_prop m d n) := by
  unfold arithmetic_prop
  cases unsafe_rsa_decrypt m d n <;> dsimp <;> infer_instance
instance (m d n : Int) : Decidable (range_prop m d n) := by
  unfold range_prop
  cases unsafe_rsa_decrypt m d n <;> dsimp <;> infer_instance
instance (m d n : Int) : Decidable (no_blinding_prop m d n) := by
  unfold no_blinding_prop
  infer_instance
instance (m d n : Int) : Decidable (errors_prop m d n) := by
  unfold errors_prop
  infer_instance
instance (m d n : Int) : Decidable (success_prop m d n) := by
  unfold success_prop
  cases unsafe_rsa_decrypt m d n <;> dsimp <;> infer_instance
instance (m d n : Int) : Decidable (Post_prop m d n) := by
  unfold Post_prop
  infer_instance

/-- Exhaustive integer samples from -bound through bound, inclusive. -/
def signedSamples (bound : Nat) : List Int :=
  (List.range (2 * bound + 1)).map (fun k => (k : Int) - (bound : Int))

/-- 6,875 triples, including both modulus signs, zero, and inverse failures. -/
def testGrid (p : Int → Int → Int → Bool) : Bool :=
  (signedSamples 12).all fun m =>
    (signedSamples 5).all fun d =>
      (signedSamples 12).all fun n => p m d n

-- PBT: exact direct-power property.
example : testGrid (fun m d n => decide (direct_power_prop m d n)) = true := by
  native_decide
-- PBT: congruence and inverse-power arithmetic.
example : testGrid (fun m d n => decide (arithmetic_prop m d n)) = true := by
  native_decide
-- PBT: canonical signed range.
example : testGrid (fun m d n => decide (range_prop m d n)) = true := by
  native_decide
-- PBT: no input applies blinding, even when decryption would raise an error.
example : testGrid (fun m d n => decide (no_blinding_prop m d n)) = true := by
  native_decide
-- PBT: both exception conditions and their priority.
example : testGrid (fun m d n => decide (errors_prop m d n)) = true := by
  native_decide
-- PBT: the exact domain of normal returns.
example : testGrid (fun m d n => decide (success_prop m d n)) = true := by
  native_decide
-- PBT: the full postcondition (tested even outside Pre).
example : testGrid (fun m d n => decide (Post_prop m d n)) = true := by
  native_decide
#eval testGrid (fun m d n => decide (Post_prop m d n))

/-- Required Hoare-style correctness theorem. All component theorems hold
also outside Pre, where they specify the exceptional outcomes. -/
theorem correctness_thm (m d n : Int) : Pre m d n → Post_prop m d n := by
  intro _hpre
  exact ⟨direct_power_thm m d n, arithmetic_thm m d n, range_thm m d n,
    no_blinding_thm m d n, errors_thm m d n, success_thm m d n⟩

/-- A structurally terminating imperative multiplication loop. Its mutable
accumulator makes the dataflow explicit; it introduces no random state.
This is a value-level model, not a claim to reproduce CPython's timing. -/
def powerLoop (base : Int) : Nat → Int → Int
  | 0, acc => acc
  | k + 1, acc => Id.run do
      let mut value := acc
      value := value * base
      return powerLoop base k value

/-- Imperative counterpart, with explicit error returns and mutable state. -/
def unsafe_rsa_decrypt_imperative (message d n : Int) : Except PowError Int := Id.run do
  if n = 0 then
    return .error .zeroModulus
  if d < 0 ∧ Int.gcd message n ≠ 1 then
    return .error .notInvertible
  let mut base := message
  if d < 0 then
    base := Int.gcdA message n
  let mut result := 1
  result := powerLoop base d.natAbs result
  result := pythonMod result n
  return .ok result

def unsafe_blinding_applied_imperative (_message _d _n : Int) : Bool := Id.run do
  let mut blinded := false
  return blinded

-- Imperative fixed tests, including the original checks.
example : unsafe_rsa_decrypt_imperative 2 3 35 = .ok 8 := by native_decide
example : unsafe_rsa_decrypt_imperative 5 7 11 = .ok 3 := by native_decide
example : unsafe_blinding_applied_imperative 2 3 35 = false := by native_decide
example : unsafe_blinding_applied_imperative 0 0 1 = false := by native_decide
example : unsafe_rsa_decrypt_imperative 2 (-1) (-35) = .ok (-17) := by native_decide
example : unsafe_rsa_decrypt_imperative 0 0 1 = .ok 0 := by native_decide
example : unsafe_rsa_decrypt_imperative 1 0 0 = .error .zeroModulus := by native_decide
example : unsafe_rsa_decrypt_imperative 5 (-1) 35 = .error .notInvertible := by native_decide
#eval (unsafe_rsa_decrypt_imperative 2 3 35, unsafe_rsa_decrypt_imperative 5 7 11)
#eval unsafe_blinding_applied_imperative 2 3 35
-- Bounded PBT of both equivalences, independently of their proofs below.
example : testGrid (fun m d n => decide
    (unsafe_rsa_decrypt m d n = unsafe_rsa_decrypt_imperative m d n ∧
     unsafe_blinding_applied m d n = unsafe_blinding_applied_imperative m d n))
    = true := by native_decide

/-- The accumulator invariant, proved for every iteration count. -/
theorem powerLoop_thm (base : Int) (k : Nat) (acc : Int) :
    powerLoop base k acc = acc * base ^ k := by
  induction k generalizing acc with
  | zero => simp [powerLoop]
  | succ k ih =>
      simp [powerLoop, ih, pow_succ]
      ring

/-- Equivalence includes all integers and both error cases; no precondition
or restriction to the bounded test grid is needed. -/
theorem decrypt_equivalence_thm (m d n : Int) :
    unsafe_rsa_decrypt m d n = unsafe_rsa_decrypt_imperative m d n := by
  by_cases hn : n = 0 <;>
    by_cases hb : d < 0 ∧ Int.gcd m n ≠ 1 <;>
      by_cases hd : d < 0 <;>
        simp [unsafe_rsa_decrypt, unsafe_rsa_decrypt_imperative,
          hn, hb, hd, powerLoop_thm]
  rfl

theorem blinding_equivalence_thm (m d n : Int) :
    unsafe_blinding_applied m d n = unsafe_blinding_applied_imperative m d n := by
  rfl

theorem equivalence_thm (m d n : Int) :
    (unsafe_rsa_decrypt m d n, unsafe_blinding_applied m d n) =
    (unsafe_rsa_decrypt_imperative m d n, unsafe_blinding_applied_imperative m d n) := by
  rw [decrypt_equivalence_thm, blinding_equivalence_thm]

end UnsafeRSABlinding
end Agent
