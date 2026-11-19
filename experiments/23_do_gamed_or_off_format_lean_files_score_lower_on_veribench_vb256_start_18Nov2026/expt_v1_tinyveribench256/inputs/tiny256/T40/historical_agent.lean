import Mathlib
namespace Agent

/-!
# The RSA example's direct modular exponentiation

This is a translation of `153_unsafeRSABlinding_safe.py`. Despite the comments
in the Python source, its executable decryptor does not sample a random value
or blind its operand: it returns `pow(message, d, n)` when `n > 1`.
`safe_blinding_applied` is a constant reporting function, not a security proof.

All three Python arguments are modeled as arbitrary signed integers. `some r`
means a normal return of `r`; `none` means the `ValueError` raised by Python's
three-argument `pow` for a negative exponent without an inverse. The `n ≤ 1`
early return happens even in that case. For a negative exponent with an
inverse, the extended Euclidean coefficient supplies that inverse. This is
an exact, unbounded-integer model, not a constant-time implementation.
-/

namespace RSA153

/-- Modular exponentiation on the `n > 1` branch of the source.
For a negative exponent Python first inverts the base, if possible. -/
def modularPow (message d n : Int) : Option Int :=
  if 0 ≤ d then
    some (message ^ d.toNat % n)
  else if Int.gcd message n = 1 then
    some (Int.gcdA message n ^ (-d).toNat % n)
  else
    none

/-- The functional translation, including the source's early return. -/
def safe_rsa_decrypt (message d n : Int) : Option Int :=
  if n ≤ 1 then some 0 else modularPow message d n

/-- Only the Python reporting function; it does not establish real blinding. -/
def safe_blinding_applied (_message _d _n : Int) : Bool := true

-- The four original assertions.
example : safe_rsa_decrypt 2 3 35 = some ((2 : Int) ^ 3 % 35) := by native_decide
example : safe_rsa_decrypt 5 7 11 = some ((5 : Int) ^ 7 % 11) := by native_decide
example : safe_blinding_applied 2 3 35 = true := by native_decide
example : safe_blinding_applied 0 0 1 = true := by native_decide
-- Additional signed-input, exponent-zero, early-return and error cases.
example : safe_rsa_decrypt (-2) 3 35 = some 27 := by native_decide
example : safe_rsa_decrypt 0 0 35 = some 1 := by native_decide
example : safe_rsa_decrypt 6 (-1) 1 = some 0 := by native_decide
example : safe_rsa_decrypt 6 (-1) (-7) = some 0 := by native_decide
example : safe_rsa_decrypt 2 (-1) 35 = some 18 := by native_decide
example : safe_rsa_decrypt 2 (-3) 35 = some 22 := by native_decide
example : safe_rsa_decrypt 5 (-1) 35 = none := by native_decide
#eval (safe_rsa_decrypt 2 3 35, safe_rsa_decrypt 5 7 11)
#eval (safe_blinding_applied 2 3 35, safe_blinding_applied 0 0 1)
#eval (safe_rsa_decrypt 2 (-1) 35, safe_rsa_decrypt 5 (-1) 35)

/-- No input restriction: the result type also represents exceptional calls. -/
def Pre (_message _d _n : Int) : Prop := True

/-- The early return is independent of both the base and the exponent. -/
def small_modulus_prop (message d n : Int) : Prop :=
  n ≤ 1 → safe_rsa_decrypt message d n = some 0

theorem small_modulus_thm (message d n : Int) : small_modulus_prop message d n := by
  intro h
  simp [safe_rsa_decrypt, h]

/-- On a valid modulus the computation is exactly direct modular power. -/
def direct_pow_prop (message d n : Int) : Prop :=
  1 < n → safe_rsa_decrypt message d n = modularPow message d n

theorem direct_pow_thm (message d n : Int) : direct_pow_prop message d n := by
  intro h
  simp [safe_rsa_decrypt, not_le.mpr h]

/-- The ordinary RSA case, without any restriction on the signed message. -/
def nonnegative_pow_prop (message d n : Int) : Prop :=
  1 < n → 0 ≤ d →
    safe_rsa_decrypt message d n = some (message ^ d.toNat % n)

theorem nonnegative_pow_thm (message d n : Int) :
    nonnegative_pow_prop message d n := by
  intro hn hd
  simp [safe_rsa_decrypt, modularPow, not_le.mpr hn, hd]

/-- For negative exponents, use a modular inverse before exponentiation. -/
def negative_pow_prop (message d n : Int) : Prop :=
  1 < n → d < 0 → Int.gcd message n = 1 →
    safe_rsa_decrypt message d n =
      some (Int.gcdA message n ^ (-d).toNat % n)

theorem negative_pow_thm (message d n : Int) :
    negative_pow_prop message d n := by
  intro hn hd hg
  simp [safe_rsa_decrypt, modularPow, not_le.mpr hn, not_le.mpr hd, hg]

/-- The coefficient used above is genuinely an inverse modulo `n`.
The unused exponent keeps the common three-argument contract interface. -/
def inverse_prop (message _d n : Int) : Prop :=
  1 < n → Int.gcd message n = 1 →
    (message * Int.gcdA message n) % n = 1

theorem inverse_thm (message d n : Int) : inverse_prop message d n := by
  intro hn hg
  have h := congrArg (fun x : Int => x % n) (Int.gcd_eq_gcd_ab message n)
  dsimp only at h
  rw [hg, Int.natCast_one, Int.add_mul_emod_self_left,
    Int.emod_eq_of_lt (by omega : (0 : Int) ≤ 1) hn] at h
  exact h.symm

/-- Exactly the source's Boolean safety report, even on exceptional inputs. -/
def blinding_applied_prop (message d n : Int) : Prop :=
  safe_blinding_applied message d n = true

theorem blinding_applied_thm (message d n : Int) :
    blinding_applied_prop message d n := by
  rfl

/-- The precise exceptional case of the source program. -/
def error_prop (message d n : Int) : Prop :=
  safe_rsa_decrypt message d n = none ↔
    1 < n ∧ d < 0 ∧ Int.gcd message n ≠ 1

theorem error_thm (message d n : Int) : error_prop message d n := by
  unfold error_prop
  by_cases hn : n ≤ 1
  · have hnot : ¬1 < n := not_lt.mpr hn
    simp [safe_rsa_decrypt, hn, hnot]
  · have hpos : 1 < n := lt_of_not_ge hn
    by_cases hd : 0 ≤ d
    · have hnot : ¬d < 0 := not_lt.mpr hd
      simp [safe_rsa_decrypt, modularPow, hn, hd, hnot]
    · have hneg : d < 0 := lt_of_not_ge hd
      by_cases hg : Int.gcd message n = 1 <;>
        simp [safe_rsa_decrypt, modularPow, hn, hd, hg, hpos, hneg]

/-- Successful results are nonnegative, and reduced modulo `n` when `n > 1`. -/
def range_prop (message d n : Int) : Prop :=
  match safe_rsa_decrypt message d n with
  | none => True
  | some result => 0 ≤ result ∧ (1 < n → result < n)

theorem range_thm (message d n : Int) : range_prop message d n := by
  unfold range_prop safe_rsa_decrypt
  by_cases hn : n ≤ 1
  · simp [hn]
  · have hnpos : 0 < n := by omega
    have hnzero : n ≠ 0 := by omega
    simp only [hn, ↓reduceIte]
    by_cases hd : 0 ≤ d
    · simp only [modularPow, if_pos hd]
      exact ⟨Int.emod_nonneg _ hnzero, fun _ => Int.emod_lt_of_pos _ hnpos⟩
    · by_cases hg : Int.gcd message n = 1
      · simp only [modularPow, if_neg hd, if_pos hg]
        exact ⟨Int.emod_nonneg _ hnzero, fun _ => Int.emod_lt_of_pos _ hnpos⟩
      · simp [modularPow, hd, hg]

/-- Complete behavioral contract, including the constant blinding report. -/
def Post_prop (message d n : Int) : Prop :=
  small_modulus_prop message d n ∧
  direct_pow_prop message d n ∧
  nonnegative_pow_prop message d n ∧
  negative_pow_prop message d n ∧
  inverse_prop message d n ∧
  blinding_applied_prop message d n ∧
  error_prop message d n ∧
  range_prop message d n

/-! ## Property-based tests

Exhaustively check the Cartesian product of messages `[-10, 10]`, exponents
`[-4, 8]`, and moduli `[-3, 19]`: 6,279 inputs per check. This includes positive
and negative messages, both exponent signs, noninvertible bases, zero powers,
and every early-return boundary. The check functions below spell out executable
forms of the propositions; they do not invoke any correctness theorem.
-/

def checkGrid (p : Int → Int → Int → Bool) : Bool :=
  (List.range 21).all fun mi =>
    (List.range 13).all fun di =>
      (List.range 23).all fun ni =>
        p ((mi : Int) - 10) ((di : Int) - 4) ((ni : Int) - 3)

def small_modulus_check (m d n : Int) : Bool :=
  decide (n ≤ 1 → safe_rsa_decrypt m d n = some 0)

def direct_pow_check (m d n : Int) : Bool :=
  decide (1 < n → safe_rsa_decrypt m d n = modularPow m d n)

def nonnegative_pow_check (m d n : Int) : Bool :=
  decide (1 < n → 0 ≤ d → safe_rsa_decrypt m d n = some (m ^ d.toNat % n))

def negative_pow_check (m d n : Int) : Bool :=
  decide (1 < n → d < 0 → Int.gcd m n = 1 →
    safe_rsa_decrypt m d n = some (Int.gcdA m n ^ (-d).toNat % n))

def inverse_check (m _d n : Int) : Bool :=
  decide (1 < n → Int.gcd m n = 1 → (m * Int.gcdA m n) % n = 1)

def blinding_applied_check (m d n : Int) : Bool :=
  safe_blinding_applied m d n == true

def error_check (m d n : Int) : Bool :=
  decide (safe_rsa_decrypt m d n = none ↔ 1 < n ∧ d < 0 ∧ Int.gcd m n ≠ 1)

def range_check (m d n : Int) : Bool :=
  match safe_rsa_decrypt m d n with
  | none => true
  | some result => decide (0 ≤ result ∧ (1 < n → result < n))

/-- Executable conjunction of precisely the eight postcondition properties. -/
def post_check (m d n : Int) : Bool :=
  small_modulus_check m d n && direct_pow_check m d n &&
  nonnegative_pow_check m d n && negative_pow_check m d n &&
  inverse_check m d n && blinding_applied_check m d n &&
  error_check m d n && range_check m d n

-- One exhaustive PBT for each `_prop`, followed by a PBT for the postcondition.
example : checkGrid small_modulus_check = true := by native_decide
example : checkGrid direct_pow_check = true := by native_decide
example : checkGrid nonnegative_pow_check = true := by native_decide
example : checkGrid negative_pow_check = true := by native_decide
example : checkGrid inverse_check = true := by native_decide
example : checkGrid blinding_applied_check = true := by native_decide
example : checkGrid error_check = true := by native_decide
example : checkGrid range_check = true := by native_decide
example : checkGrid post_check = true := by native_decide
#eval checkGrid post_check

/-- All integer inputs satisfy the contract, with exceptional outcomes modeled. -/
theorem correctness_thm (message d n : Int) :
    Pre message d n → Post_prop message d n := by
  intro _
  exact ⟨small_modulus_thm message d n, direct_pow_thm message d n,
    nonnegative_pow_thm message d n, negative_pow_thm message d n,
    inverse_thm message d n, blinding_applied_thm message d n,
    error_thm message d n, range_thm message d n⟩

/-! ## Imperative translation -/

/-- The early return and local result variable of the Python implementation.
The negative-power branch makes the built-in `pow` error explicit. -/
def safe_rsa_decrypt_imp (message d n : Int) : Option Int := Id.run do
  if n ≤ 1 then
    return some 0
  let mut result : Option Int := none
  if 0 ≤ d then
    result := some (message ^ d.toNat % n)
  else if Int.gcd message n = 1 then
    result := some (Int.gcdA message n ^ (-d).toNat % n)
  return result

def safe_blinding_applied_imp (_message _d _n : Int) : Bool := Id.run do
  let mut applied := false
  applied := true
  return applied

-- Imperative versions of all four original tests, plus edge cases.
example : safe_rsa_decrypt_imp 2 3 35 = some ((2 : Int) ^ 3 % 35) := by native_decide
example : safe_rsa_decrypt_imp 5 7 11 = some ((5 : Int) ^ 7 % 11) := by native_decide
example : safe_blinding_applied_imp 2 3 35 = true := by native_decide
example : safe_blinding_applied_imp 0 0 1 = true := by native_decide
example : safe_rsa_decrypt_imp (-2) 3 35 = some 27 := by native_decide
example : safe_rsa_decrypt_imp 0 0 35 = some 1 := by native_decide
example : safe_rsa_decrypt_imp 6 (-1) 1 = some 0 := by native_decide
example : safe_rsa_decrypt_imp 6 (-1) (-7) = some 0 := by native_decide
example : safe_rsa_decrypt_imp 2 (-1) 35 = some 18 := by native_decide
example : safe_rsa_decrypt_imp 2 (-3) 35 = some 22 := by native_decide
example : safe_rsa_decrypt_imp 5 (-1) 35 = none := by native_decide
#eval (safe_rsa_decrypt_imp 2 3 35, safe_rsa_decrypt_imp 5 7 11)
#eval (safe_blinding_applied_imp 2 3 35, safe_blinding_applied_imp 0 0 1)
#eval (safe_rsa_decrypt_imp 2 (-1) 35, safe_rsa_decrypt_imp 5 (-1) 35)

-- An exhaustive comparison is additional evidence, not the equivalence proof.
example : checkGrid (fun m d n =>
    safe_rsa_decrypt m d n == safe_rsa_decrypt_imp m d n) = true := by native_decide
example : checkGrid (fun m d n =>
    safe_blinding_applied m d n == safe_blinding_applied_imp m d n) = true := by
  native_decide

/-- Functional/imperative equivalence covers successful and exceptional calls. -/
theorem safe_rsa_decrypt_equiv_thm (message d n : Int) :
    safe_rsa_decrypt message d n = safe_rsa_decrypt_imp message d n := by
  by_cases hn : n ≤ 1 <;> by_cases hd : 0 ≤ d <;>
    by_cases hg : Int.gcd message n = 1 <;>
    simp [safe_rsa_decrypt, modularPow, safe_rsa_decrypt_imp, hn, hd, hg]

theorem safe_blinding_applied_equiv_thm (message d n : Int) :
    safe_blinding_applied message d n = safe_blinding_applied_imp message d n := by
  rfl

end RSA153
end Agent
