import Mathlib

/-!
# 23_is_prime: Primality Test for Non-Negative Integers

This module formalizes the Python `is_prime` function in Lean 4.
A prime number is a natural number greater than 1 that is not divisible
by any positive integer other than 1 and itself.

Edge cases:
- `0` and `1` are not prime.
- Negative inputs violate the precondition `Pre n` (`n ≥ 0`).

The algorithm checks edge cases (`n ≤ 1`, `n ≤ 3`, multiples of `2` or `3`)
and then tests all candidate divisors of the form `6k ± 1` (i.e., `5 + 6k` and `7 + 6k`)
up to `⌊√n⌋`.
-/

namespace «23_is_prime»

/-! ## Implementation (Functional) -/

/--
Check if a non-negative integer `n` is prime.
A prime number is a natural number greater than 1 that is not divisible by
any positive integer other than 1 and itself.
-/
def is_prime (n : Int) : Bool :=
  if n ≤ 1 then false
  else if n ≤ 3 then true
  else if n % 2 == 0 || n % 3 == 0 then false
  else
    let m := n.toNat
    let limit := Nat.sqrt m
    (List.range ((limit + 1) / 6)).all fun k =>
      let i := 5 + 6 * k
      m % i != 0 && m % (i + 2) != 0

/-! ## Unit Tests -/

#eval is_prime 2
#eval is_prime 4
#eval is_prime 0
#eval is_prime 7
#eval is_prime 1
#eval is_prime 3
#eval is_prime 25
#eval is_prime 97

example : is_prime 2 = true := by native_decide
example : is_prime 4 = false := by native_decide
example : is_prime 0 = false := by native_decide
example : is_prime 7 = true := by native_decide
example : is_prime 1 = false := by native_decide
example : is_prime 3 = true := by native_decide
example : is_prime 5 = true := by native_decide
example : is_prime 9 = false := by native_decide
example : is_prime 25 = false := by native_decide
example : is_prime 29 = true := by native_decide
example : is_prime 49 = false := by native_decide
example : is_prime 97 = true := by native_decide
example : is_prime 121 = false := by native_decide
example : is_prime (-1) = false := by native_decide

/-! ## Pre-condition -/

/--
Pre-condition for `is_prime`: input `n` must be a non-negative integer.
-/
def Pre (n : Int) : Prop := n ≥ 0

instance (n : Int) : Decidable (Pre n) :=
  inferInstanceAs (Decidable (n ≥ 0))

/-! ## Helper Lemmas for Primality Proof -/

theorem sqrt_add_two_lt (m : Nat) (h : 5 ≤ m.sqrt) : m.sqrt + 2 < m := by
  have h1 : m.sqrt * m.sqrt ≤ m := Nat.sqrt_le m
  have h2 : 5 * m.sqrt ≤ m.sqrt * m.sqrt := Nat.mul_le_mul_right m.sqrt h
  omega

theorem minFac_cases (p s : Nat) (hp_le : p ≤ s) (hp_ge : 2 ≤ p)
    (hp2 : p % 2 ≠ 0) (hp3 : p % 3 ≠ 0) :
    (p = 5 + 6 * ((p - 5) / 6) ∧ (p - 5) / 6 < (s + 1) / 6) ∨
    (p = 5 + 6 * ((p - 7) / 6) + 2 ∧ (p - 7) / 6 < (s + 1) / 6) := by
  have : p % 6 = 1 ∨ p % 6 = 5 := by omega
  omega

theorem is_prime_iff_natPrime (n : Int) : is_prime n = true ↔ Nat.Prime n.toNat := by
  unfold is_prime
  by_cases h1 : n ≤ 1
  · simp only [h1, ↓reduceIte, Bool.false_eq_true, false_iff]
    intro hp
    have := hp.two_le
    omega
  · by_cases h2 : n ≤ 3
    · simp only [h1, h2, ↓reduceIte, true_iff]
      have : n.toNat = 2 ∨ n.toNat = 3 := by omega
      rcases this with h | h <;> rw [h]
      · exact Nat.prime_two
      · exact Nat.prime_three
    · by_cases h3 : (n % 2 == 0 || n % 3 == 0) = true
      · simp only [h1, h2, h3, ↓reduceIte, Bool.false_eq_true, false_iff]
        intro hp
        simp only [Bool.or_eq_true, beq_iff_eq] at h3
        rcases h3 with h3 | h3
        · have hdvd : 2 ∣ n.toNat := by omega
          rcases hp.eq_one_or_self_of_dvd 2 hdvd with h | h <;> omega
        · have hdvd : 3 ∣ n.toNat := by omega
          rcases hp.eq_one_or_self_of_dvd 3 hdvd with h | h <;> omega
      · simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte, List.all_eq_true, List.mem_range,
          Bool.and_eq_true, bne_iff_ne, ne_eq]
        constructor
        · intro hall
          by_contra hnp
          have hm1 : n.toNat ≠ 1 := by omega
          have hm0 : 0 < n.toNat := by omega
          have hp_prime : Nat.Prime n.toNat.minFac := Nat.minFac_prime hm1
          have hp_dvd : n.toNat.minFac ∣ n.toNat := Nat.minFac_dvd n.toNat
          have hp_sq : n.toNat.minFac ^ 2 ≤ n.toNat := Nat.minFac_sq_le_self hm0 hnp
          have hp_le_sqrt : n.toNat.minFac ≤ n.toNat.sqrt := by
            rw [Nat.le_sqrt]
            simpa [sq] using hp_sq
          have hp_ge2 : 2 ≤ n.toNat.minFac := hp_prime.two_le
          simp only [Bool.or_eq_true, beq_iff_eq, not_or] at h3
          have hnd2 : ¬ (2 ∣ n.toNat) := by omega
          have hnd3 : ¬ (3 ∣ n.toNat) := by omega
          have hp2 : n.toNat.minFac % 2 ≠ 0 := by
            intro h
            exact hnd2 (dvd_trans (Nat.dvd_of_mod_eq_zero h) hp_dvd)
          have hp3 : n.toNat.minFac % 3 ≠ 0 := by
            intro h
            exact hnd3 (dvd_trans (Nat.dvd_of_mod_eq_zero h) hp_dvd)
          have hp_mod : n.toNat % n.toNat.minFac = 0 := Nat.mod_eq_zero_of_dvd hp_dvd
          rcases minFac_cases n.toNat.minFac n.toNat.sqrt hp_le_sqrt hp_ge2 hp2 hp3 with
            ⟨heq, hlt⟩ | ⟨heq, hlt⟩
          · have hne := (hall _ hlt).1
            rw [← heq] at hne
            exact hne hp_mod
          · have hne := (hall _ hlt).2
            rw [← heq] at hne
            exact hne hp_mod
        · intro hp k hk
          have hsqrt : 5 ≤ n.toNat.sqrt := by omega
          have : n.toNat.sqrt + 2 < n.toNat := sqrt_add_two_lt n.toNat hsqrt
          constructor
          · intro hmod
            have hdvd : (5 + 6 * k) ∣ n.toNat := Nat.dvd_of_mod_eq_zero hmod
            rcases hp.eq_one_or_self_of_dvd (5 + 6 * k) hdvd with h | h <;> omega
          · intro hmod
            have hdvd : (5 + 6 * k + 2) ∣ n.toNat := Nat.dvd_of_mod_eq_zero hmod
            rcases hp.eq_one_or_self_of_dvd (5 + 6 * k + 2) hdvd with h | h <;> omega

theorem natPrime_iff_no_proper_divisor (n : Int) :
    Nat.Prime n.toNat ↔ (n > 1 ∧ ∀ d : Int, 1 < d → d < n → n % d ≠ 0) := by
  rw [Nat.prime_def_lt']
  constructor
  · rintro ⟨h2, hall⟩
    refine ⟨by omega, fun d hd1 hd2 hmod => ?_⟩
    have h1 : 2 ≤ d.toNat := by omega
    have h2' : d.toNat < n.toNat := by omega
    have hdvd : d.toNat ∣ n.toNat := by
      rw [← Int.ofNat_dvd, Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
      exact Int.dvd_of_emod_eq_zero hmod
    exact hall d.toNat h1 h2' hdvd
  · rintro ⟨hn1, hall⟩
    refine ⟨by omega, fun m hm1 hm2 hdvd => ?_⟩
    have hmod : n % (m : Int) = 0 := by
      apply Int.emod_eq_zero_of_dvd
      have := Int.ofNat_dvd.mpr hdvd
      rwa [Int.toNat_of_nonneg (by omega)] at this
    exact hall (m : Int) (by omega) (by omega) hmod

/-! ## Property Propositions and Theorems -/

/--
Property 1: Numbers less than or equal to 1 (including 0 and 1) are not prime.
-/
def non_positive_or_one_not_prime_prop (n : Int) : Prop :=
  n ≤ 1 → is_prime n = false

instance (n : Int) : Decidable (non_positive_or_one_not_prime_prop n) :=
  inferInstanceAs (Decidable (n ≤ 1 → is_prime n = false))

theorem non_positive_or_one_not_prime_thm (n : Int) (_h : Pre n) :
    non_positive_or_one_not_prime_prop n := by
  intro hn1
  unfold is_prime
  simp [hn1]

/--
Property 2: 2 and 3 are prime.
-/
def small_primes_prop (n : Int) : Prop :=
  (n = 2 ∨ n = 3) → is_prime n = true

instance (n : Int) : Decidable (small_primes_prop n) :=
  inferInstanceAs (Decidable ((n = 2 ∨ n = 3) → is_prime n = true))

theorem small_primes_thm (n : Int) (_h : Pre n) : small_primes_prop n := by
  rintro (rfl | rfl) <;> rfl

/--
Property 3: Every even integer strictly greater than 2 is composite (`is_prime n = false`).
-/
def even_gt_two_not_prime_prop (n : Int) : Prop :=
  (n > 2 ∧ n % 2 = 0) → is_prime n = false

instance (n : Int) : Decidable (even_gt_two_not_prime_prop n) :=
  inferInstanceAs (Decidable ((n > 2 ∧ n % 2 = 0) → is_prime n = false))

theorem even_gt_two_not_prime_thm (n : Int) (_h : Pre n) :
    even_gt_two_not_prime_prop n := by
  rintro ⟨hgt2, heven⟩
  unfold is_prime
  have h1 : ¬ (n ≤ 1) := by omega
  have h2 : ¬ (n ≤ 3) := by omega
  simp [h1, h2, heven]

/--
Property 4: Every multiple of 3 strictly greater than 3 is composite (`is_prime n = false`).
-/
def multiple_of_three_gt_three_not_prime_prop (n : Int) : Prop :=
  (n > 3 ∧ n % 3 = 0) → is_prime n = false

instance (n : Int) : Decidable (multiple_of_three_gt_three_not_prime_prop n) :=
  inferInstanceAs (Decidable ((n > 3 ∧ n % 3 = 0) → is_prime n = false))

theorem multiple_of_three_gt_three_not_prime_thm (n : Int) (_h : Pre n) :
    multiple_of_three_gt_three_not_prime_prop n := by
  rintro ⟨hgt3, hdiv3⟩
  unfold is_prime
  have h1 : ¬ (n ≤ 1) := by omega
  have h2 : ¬ (n ≤ 3) := by omega
  simp [h1, h2, hdiv3]

/--
Property 5: Any number reported prime by `is_prime` is strictly greater than 1.
-/
def prime_gt_one_prop (n : Int) : Prop :=
  is_prime n = true → n > 1

instance (n : Int) : Decidable (prime_gt_one_prop n) :=
  inferInstanceAs (Decidable (is_prime n = true → n > 1))

theorem prime_gt_one_thm (n : Int) (_h : Pre n) : prime_gt_one_prop n := by
  intro hp
  rw [is_prime_iff_natPrime] at hp
  have := hp.two_le
  omega

/--
Property 6 (Divisor specification): `is_prime n = true` iff `n > 1` and `n` is not
divisible by any integer `d` with `1 < d < n`.
-/
def no_proper_divisor_prop (n : Int) : Prop :=
  (is_prime n = true) ↔ (n > 1 ∧ ∀ d : Int, 1 < d → d < n → n % d ≠ 0)

instance (n : Int) : Decidable (∀ d : Int, 1 < d → d < n → n % d ≠ 0) :=
  decidable_of_iff (∀ d ∈ Finset.Ioo 1 n, n % d ≠ 0) (by
    simp [Finset.mem_Ioo, and_imp])

instance (n : Int) : Decidable (no_proper_divisor_prop n) :=
  inferInstanceAs (Decidable ((is_prime n = true) ↔ (n > 1 ∧ ∀ d : Int, 1 < d → d < n → n % d ≠ 0)))

theorem no_proper_divisor_thm (n : Int) (_h : Pre n) : no_proper_divisor_prop n := by
  unfold no_proper_divisor_prop
  rw [is_prime_iff_natPrime, natPrime_iff_no_proper_divisor]

/--
Property 7 (Mathlib `Nat.Prime` equivalence): `is_prime n = true` iff `Nat.Prime n.toNat`.
-/
def nat_prime_iff_prop (n : Int) : Prop :=
  (is_prime n = true) ↔ Nat.Prime n.toNat

instance (n : Int) : Decidable (nat_prime_iff_prop n) :=
  inferInstanceAs (Decidable ((is_prime n = true) ↔ Nat.Prime n.toNat))

theorem nat_prime_iff_thm (n : Int) (_h : Pre n) : nat_prime_iff_prop n :=
  is_prime_iff_natPrime n

/-! ## Post-condition -/

/--
Post-condition for `is_prime`: conjunction of all specification properties.
-/
def Post_prop (n : Int) : Prop :=
  non_positive_or_one_not_prime_prop n ∧
  small_primes_prop n ∧
  even_gt_two_not_prime_prop n ∧
  multiple_of_three_gt_three_not_prime_prop n ∧
  prime_gt_one_prop n ∧
  no_proper_divisor_prop n ∧
  nat_prime_iff_prop n

instance (n : Int) : Decidable (Post_prop n) :=
  inferInstanceAs (Decidable (
    non_positive_or_one_not_prime_prop n ∧
    small_primes_prop n ∧
    even_gt_two_not_prime_prop n ∧
    multiple_of_three_gt_three_not_prime_prop n ∧
    prime_gt_one_prop n ∧
    no_proper_divisor_prop n ∧
    nat_prime_iff_prop n))

/-! ## Property-Based Tests (PBTs) -/

#eval Plausible.Testable.check (∀ n : Int, Pre n → decide (non_positive_or_one_not_prime_prop n) = true)
#eval Plausible.Testable.check (∀ n : Int, Pre n → decide (small_primes_prop n) = true)
#eval Plausible.Testable.check (∀ n : Int, Pre n → decide (even_gt_two_not_prime_prop n) = true)
#eval Plausible.Testable.check (∀ n : Int, Pre n → decide (multiple_of_three_gt_three_not_prime_prop n) = true)
#eval Plausible.Testable.check (∀ n : Int, Pre n → decide (prime_gt_one_prop n) = true)
#eval Plausible.Testable.check (∀ n : Int, Pre n → decide (no_proper_divisor_prop n) = true)
#eval Plausible.Testable.check (∀ n : Int, Pre n → decide (nat_prime_iff_prop n) = true)
#eval Plausible.Testable.check (∀ n : Int, Pre n → decide (Post_prop n) = true)

-- Bounded exhaustive property-based tests on [0, 200)
example : (List.range 200).all (fun k => decide (non_positive_or_one_not_prime_prop (Int.ofNat k))) = true := by native_decide
example : (List.range 200).all (fun k => decide (small_primes_prop (Int.ofNat k))) = true := by native_decide
example : (List.range 200).all (fun k => decide (even_gt_two_not_prime_prop (Int.ofNat k))) = true := by native_decide
example : (List.range 200).all (fun k => decide (multiple_of_three_gt_three_not_prime_prop (Int.ofNat k))) = true := by native_decide
example : (List.range 200).all (fun k => decide (prime_gt_one_prop (Int.ofNat k))) = true := by native_decide
example : (List.range 200).all (fun k => decide (no_proper_divisor_prop (Int.ofNat k))) = true := by native_decide
example : (List.range 200).all (fun k => decide (nat_prime_iff_prop (Int.ofNat k))) = true := by native_decide
example : (List.range 200).all (fun k => decide (Post_prop (Int.ofNat k))) = true := by native_decide

/-! ## Correctness Theorem (Pre -> Post) -/

/--
Main correctness theorem: for any integer `n` satisfying `Pre n` (`n ≥ 0`),
`Post_prop n` holds.
-/
theorem is_prime_correct (n : Int) (h : Pre n) : Post_prop n :=
  ⟨non_positive_or_one_not_prime_thm n h,
   small_primes_thm n h,
   even_gt_two_not_prime_thm n h,
   multiple_of_three_gt_three_not_prime_thm n h,
   prime_gt_one_thm n h,
   no_proper_divisor_thm n h,
   nat_prime_iff_thm n h⟩

/-! ## Imperative Implementation -/

/--
Imperative implementation of `is_prime` using `Id.run do` with mutable state and early exit.
-/
def is_prime_imp (n : Int) : Bool := Id.run do
  if n ≤ 1 then
    return false
  if n ≤ 3 then
    return true
  if n % 2 == 0 || n % 3 == 0 then
    return false
  let m := n.toNat
  let limit := Nat.sqrt m
  let mut result := true
  for k in List.range ((limit + 1) / 6) do
    let i := 5 + 6 * k
    if m % i == 0 || m % (i + 2) == 0 then
      result := false
      break
  return result

/-! ## Imperative Tests -/

#eval is_prime_imp 2
#eval is_prime_imp 4
#eval is_prime_imp 0
#eval is_prime_imp 7
#eval is_prime_imp 1
#eval is_prime_imp 3
#eval is_prime_imp 25
#eval is_prime_imp 97

example : is_prime_imp 2 = true := by native_decide
example : is_prime_imp 4 = false := by native_decide
example : is_prime_imp 0 = false := by native_decide
example : is_prime_imp 7 = true := by native_decide
example : is_prime_imp 1 = false := by native_decide
example : is_prime_imp 3 = true := by native_decide
example : is_prime_imp 5 = true := by native_decide
example : is_prime_imp 9 = false := by native_decide
example : is_prime_imp 25 = false := by native_decide
example : is_prime_imp 29 = true := by native_decide
example : is_prime_imp 49 = false := by native_decide
example : is_prime_imp 97 = true := by native_decide
example : is_prime_imp 121 = false := by native_decide
example : is_prime_imp (-1) = false := by native_decide

#eval Plausible.Testable.check (∀ n : Int, Pre n → is_prime n = is_prime_imp n)
example : (List.range 200).all (fun k => is_prime (Int.ofNat k) == is_prime_imp (Int.ofNat k)) = true := by native_decide

/-! ## Equivalence Theorem (Functional = Imperative) -/

theorem forIn_all_eq (xs : List Nat) (m : Nat) :
    (Id.run do
      let mut result := true
      for k in xs do
        let i := 5 + 6 * k
        if m % i == 0 || m % (i + 2) == 0 then
          result := false
          break
      return result) =
    xs.all (fun k => let i := 5 + 6 * k; m % i != 0 && m % (i + 2) != 0) := by
  simp only [Id.run, Bind.bind, Pure.pure]
  induction xs with
  | nil => rfl
  | cons k xs ih =>
    simp only [List.forIn_cons, List.all_cons, Bind.bind, Pure.pure, bne]
    cases (m % (5 + 6 * k) == 0) <;> cases (m % (5 + 6 * k + 2) == 0) <;>
      simp only [Bool.false_or, Bool.true_or, Bool.not_false, Bool.not_true,
        Bool.false_and, Bool.true_and, ↓reduceIte, Bool.false_eq_true]
    exact ih

/--
Equivalence theorem: the functional implementation `is_prime` and the imperative
implementation `is_prime_imp` produce identical results for all inputs `n : Int`.
-/
theorem is_prime_equiv (n : Int) : is_prime n = is_prime_imp n := by
  unfold is_prime is_prime_imp
  by_cases h1 : n ≤ 1
  · simp [h1, Id.run, Pure.pure]
  · by_cases h2 : n ≤ 3
    · simp [h1, h2, Id.run, Bind.bind, Pure.pure]
    · by_cases h3 : (n % 2 == 0 || n % 3 == 0) = true
      · simp [h1, h2, h3, Id.run, Bind.bind, Pure.pure]
      · simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte]
        exact (forIn_all_eq (List.range ((n.toNat.sqrt + 1) / 6)) n.toNat).symm

/--
Equivalence under precondition `Pre n`.
-/
theorem is_prime_equiv_under_pre (n : Int) (_h : Pre n) : is_prime n = is_prime_imp n :=
  is_prime_equiv n

end «23_is_prime»
