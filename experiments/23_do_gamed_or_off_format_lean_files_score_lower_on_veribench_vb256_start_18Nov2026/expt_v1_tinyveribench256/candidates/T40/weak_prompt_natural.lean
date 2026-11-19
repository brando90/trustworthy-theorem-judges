import Mathlib

/-!
# Direct modular exponentiation without blinding

This is a Lean 4 translation of a small Python module.

* `safe_rsa_decrypt message d n` returns `0` when `n ≤ 1`. Otherwise it returns
  `pow(message, d, n)`. For a negative exponent, Python first inverts `message`
  modulo `n` and raises `ValueError` when no inverse exists. No blinding is done.
* `safe_blinding_applied message d n` always returns `True`.

Python's `ValueError` is modeled as `Except.error PowError.notInvertible`.
For a positive modulus, Python's `%` and Lean's `Int.emod` (`%`) agree. So every
successful result lies in `[0, n)`.
-/

namespace SafeRsa

/-- The exception that Python's three-argument `pow` raises in this program:
`ValueError: base is not invertible for the given modulus`. -/
inductive PowError where
  | notInvertible
  deriving DecidableEq, Repr

/-- The modular inverse that Python's `pow` uses for a negative exponent. When
`gcd a n = 1`, it returns the Bézout coefficient of `a`, reduced into `[0, n)` for
`n > 0`. Otherwise it returns `none`, which is the case where Python raises
`ValueError`. -/
def modInverse (a n : Int) : Option Int :=
  if Int.gcd a n = 1 then some (Int.gcdA a n % n) else none

/-- The Lean version of `safe_rsa_decrypt`. It returns `0` when `n ≤ 1`. Otherwise
it returns `pow(message, d, n)`. A negative `d` uses the modular inverse and fails
with `PowError.notInvertible` when `message` has no inverse modulo `n`. No blinding
is done. -/
def safeRsaDecrypt (message d n : Int) : Except PowError Int :=
  if n ≤ 1 then
    .ok 0
  else if 0 ≤ d then
    .ok (message ^ d.toNat % n)
  else
    match modInverse message n with
    | some inv => .ok (inv ^ d.natAbs % n)
    | none => .error .notInvertible

/-- The Lean version of `safe_blinding_applied`. It always returns `true` and
ignores its arguments. It neither performs nor checks blinding. -/
def safeBlindingApplied (_message _d _n : Int) : Bool := true

/-- Python's `check()`: the fixed examples, combined into one Boolean. -/
def check : Bool :=
  safeBlindingApplied 2 3 35 == true &&
  safeBlindingApplied 0 0 1 == true &&
  safeBlindingApplied 2 3 0 == true &&
  safeBlindingApplied 1 1 1 == true &&
  safeBlindingApplied 2 2 2 == true

/-! ## The blinding placeholder -/

theorem safeBlindingApplied_eq_true (m d n : Int) : safeBlindingApplied m d n = true := rfl

/-- The placeholder ignores all of its inputs. -/
theorem safeBlindingApplied_const (m d n m' d' n' : Int) :
    safeBlindingApplied m d n = safeBlindingApplied m' d' n' := rfl

/-- Every assertion in Python's `check()` holds. -/
theorem check_eq_true : check = true := by decide

theorem check_examples :
    safeBlindingApplied 2 3 35 = true ∧ safeBlindingApplied 0 0 1 = true ∧
      safeBlindingApplied 2 3 0 = true ∧ safeBlindingApplied 1 1 1 = true ∧
      safeBlindingApplied 2 2 2 = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## The modular inverse -/

/-- Reducing the right factor modulo `n` does not change a product modulo `n`. -/
theorem mul_emod_right_reduce (a b n : Int) : a * (b % n) % n = a * b % n := by
  rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]

theorem modInverse_of_coprime {a n : Int} (hg : Int.gcd a n = 1) :
    modInverse a n = some (Int.gcdA a n % n) := by
  simp only [modInverse, if_pos hg]

theorem modInverse_of_not_coprime {a n : Int} (hg : Int.gcd a n ≠ 1) :
    modInverse a n = none := by
  simp only [modInverse, if_neg hg]

/-- The inverse fails to exist exactly when `a` and `n` are not coprime. -/
theorem modInverse_eq_none_iff {a n : Int} : modInverse a n = none ↔ Int.gcd a n ≠ 1 := by
  constructor
  · intro h hg
    rw [modInverse_of_coprime hg] at h
    cases h
  · exact modInverse_of_not_coprime

/-- Correctness: the returned value really is an inverse modulo `n`. -/
theorem modInverse_spec {a n b : Int} (h : modInverse a n = some b) :
    a * b % n = 1 % n := by
  by_cases hg : Int.gcd a n = 1
  · rw [modInverse_of_coprime hg] at h
    cases h
    have hb : a * Int.gcdA a n + n * Int.gcdB a n = 1 := by
      have h0 := Int.gcd_eq_gcd_ab a n
      rw [hg] at h0
      exact_mod_cast h0.symm
    rw [mul_emod_right_reduce,
      show a * Int.gcdA a n = 1 + n * (-Int.gcdB a n) by linear_combination hb,
      Int.add_mul_emod_self_left]
  · rw [modInverse_of_not_coprime hg] at h
    cases h

/-! ## Exponentiation -/

variable {m d n r : Int}

/-- A degenerate modulus (`n ≤ 1`) always gives `0`, even for a negative exponent. -/
theorem safeRsaDecrypt_of_le_one (h : n ≤ 1) : safeRsaDecrypt m d n = .ok 0 := by
  simp only [safeRsaDecrypt, if_pos h]

/-- A nonnegative exponent never fails. The result is `m ^ d % n`. -/
theorem safeRsaDecrypt_of_nonneg (hn : 1 < n) (hd : 0 ≤ d) :
    safeRsaDecrypt m d n = .ok (m ^ d.toNat % n) := by
  have h1 : ¬ n ≤ 1 := by omega
  simp only [safeRsaDecrypt, if_neg h1, if_pos hd]

/-- A negative exponent with an invertible base uses the inverse. -/
theorem safeRsaDecrypt_neg_of_coprime (hn : 1 < n) (hd : d < 0) (hg : Int.gcd m n = 1) :
    safeRsaDecrypt m d n = .ok ((Int.gcdA m n % n) ^ d.natAbs % n) := by
  have h1 : ¬ n ≤ 1 := by omega
  have h2 : ¬ 0 ≤ d := by omega
  simp only [safeRsaDecrypt, if_neg h1, if_neg h2, modInverse_of_coprime hg]

/-- A negative exponent with a non-invertible base raises `ValueError`. -/
theorem safeRsaDecrypt_neg_of_not_coprime (hn : 1 < n) (hd : d < 0)
    (hg : Int.gcd m n ≠ 1) :
    safeRsaDecrypt m d n = .error .notInvertible := by
  have h1 : ¬ n ≤ 1 := by omega
  have h2 : ¬ 0 ≤ d := by omega
  simp only [safeRsaDecrypt, if_neg h1, if_neg h2, modInverse_of_not_coprime hg]

/-- The exact conditions under which the Python function raises. -/
theorem safeRsaDecrypt_eq_error_iff :
    safeRsaDecrypt m d n = .error .notInvertible ↔ 1 < n ∧ d < 0 ∧ Int.gcd m n ≠ 1 := by
  constructor
  · intro h
    by_cases hn : n ≤ 1
    · rw [safeRsaDecrypt_of_le_one hn] at h
      cases h
    · have hn' : 1 < n := by omega
      by_cases hd : 0 ≤ d
      · rw [safeRsaDecrypt_of_nonneg hn' hd] at h
        cases h
      · have hd' : d < 0 := by omega
        refine ⟨hn', hd', fun hg => ?_⟩
        rw [safeRsaDecrypt_neg_of_coprime hn' hd' hg] at h
        cases h
  · rintro ⟨hn, hd, hg⟩
    exact safeRsaDecrypt_neg_of_not_coprime hn hd hg

/-- Every successful result for a proper modulus lies in `[0, n)`. -/
theorem safeRsaDecrypt_range (hn : 1 < n) (h : safeRsaDecrypt m d n = .ok r) :
    0 ≤ r ∧ r < n := by
  have hn0 : n ≠ 0 := by omega
  have hpos : 0 < n := by omega
  by_cases hd : 0 ≤ d
  · rw [safeRsaDecrypt_of_nonneg hn hd] at h
    cases h
    exact ⟨Int.emod_nonneg _ hn0, Int.emod_lt_of_pos _ hpos⟩
  · have hd' : d < 0 := by omega
    by_cases hg : Int.gcd m n = 1
    · rw [safeRsaDecrypt_neg_of_coprime hn hd' hg] at h
      cases h
      exact ⟨Int.emod_nonneg _ hn0, Int.emod_lt_of_pos _ hpos⟩
    · rw [safeRsaDecrypt_neg_of_not_coprime hn hd' hg] at h
      cases h

/-- Python's `pow(m, 0, n)` is `1` for any `n > 1`, including `m = 0`. -/
theorem safeRsaDecrypt_zero_exp (hn : 1 < n) : safeRsaDecrypt m 0 n = .ok 1 := by
  rw [safeRsaDecrypt_of_nonneg hn le_rfl]
  have h : m ^ (0 : Int).toNat % n = 1 := by
    rw [show (0 : Int).toNat = 0 from rfl, pow_zero]
    exact Int.emod_eq_of_lt (by norm_num) hn
  rw [h]

/-- Raising `1` to a nonnegative power gives `1`. -/
theorem safeRsaDecrypt_one_base (hn : 1 < n) (hd : 0 ≤ d) :
    safeRsaDecrypt 1 d n = .ok 1 := by
  rw [safeRsaDecrypt_of_nonneg hn hd]
  have h : (1 : Int) ^ d.toNat % n = 1 := by
    rw [one_pow]
    exact Int.emod_eq_of_lt (by norm_num) hn
  rw [h]

/-- For a nonnegative exponent, the result depends only on the message modulo `n`. -/
theorem safeRsaDecrypt_add_mul (hn : 1 < n) (hd : 0 ≤ d) (k : Int) :
    safeRsaDecrypt (m + n * k) d n = safeRsaDecrypt m d n := by
  have hmod : (m + n * k) % n = m % n := by rw [Int.add_mul_emod_self_left]
  have hmod' : Int.ModEq n (m + n * k) m := hmod
  have hpow : (m + n * k) ^ d.toNat % n = m ^ d.toNat % n := hmod'.pow d.toNat
  rw [safeRsaDecrypt_of_nonneg hn hd, safeRsaDecrypt_of_nonneg hn hd, hpow]

/-- Correctness for a negative exponent: the result is the inverse of `m ^ |d|` modulo `n`. -/
theorem safeRsaDecrypt_neg_inverse (hn : 1 < n) (hd : d < 0)
    (h : safeRsaDecrypt m d n = .ok r) : m ^ d.natAbs * r % n = 1 := by
  by_cases hg : Int.gcd m n = 1
  · rw [safeRsaDecrypt_neg_of_coprime hn hd hg] at h
    cases h
    have hinv : Int.ModEq n (m * (Int.gcdA m n % n)) 1 :=
      modInverse_spec (modInverse_of_coprime hg)
    have hpow := hinv.pow d.natAbs
    rw [one_pow, mul_pow] at hpow
    have hmod : m ^ d.natAbs * (Int.gcdA m n % n) ^ d.natAbs % n = 1 % n := hpow
    rw [mul_emod_right_reduce, hmod]
    exact Int.emod_eq_of_lt (by norm_num) hn
  · rw [safeRsaDecrypt_neg_of_not_coprime hn hd hg] at h
    cases h

/-! ## Concrete runs -/

-- Python: pow(2, 3, 35) == 8
example : safeRsaDecrypt 2 3 35 = .ok 8 := by rfl

-- Python: pow(-2, 3, 5) == 2 (floor and Euclidean mod agree for n > 0)
example : safeRsaDecrypt (-2) 3 5 = .ok 2 := by rfl

-- n <= 1 returns 0 before pow is called, even with a negative exponent
example : safeRsaDecrypt 7 (-5) 1 = .ok 0 := by rfl

-- Python: pow(2, -1, 4) raises ValueError
example : safeRsaDecrypt 2 (-1) 4 = .error .notInvertible :=
  safeRsaDecrypt_neg_of_not_coprime (by norm_num) (by norm_num) (by decide)

end SafeRsa

/-! TL;DR: `safeRsaDecrypt` models Python's `pow(message, d, n)`, with `ValueError`
represented as `PowError.notInvertible`. `safeBlindingApplied` is constantly `true`.
The theorems cover the `n ≤ 1` case, the `[0, n)` result range, the exact error
conditions, and that the inverse is correct. This file was not compiled here, so
check it with `lake build` against current Mathlib. -/
