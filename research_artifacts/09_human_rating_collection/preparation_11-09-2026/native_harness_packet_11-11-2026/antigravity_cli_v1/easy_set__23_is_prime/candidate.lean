import Mathlib

/-!
# Check if a Non-Negative Integer is Prime

This module translates the Python `is_prime` function into Lean 4, following the
VeriBench specification format.

Given a non-negative integer `n`, `is_prime n` checks whether `n` is a prime number
(a natural number greater than `1` that is not divisible by any positive integer
other than `1` and itself) using trial division by `2`, `3`, and integers of the
form `6k ± 1` up to `⌊√n⌋`.
-/

namespace «23_is_prime»

/-! ## Implementation (Functional) -/

/--
Helper function that checks whether `n` has any divisor of the form `i` or `i + 2`
(representing `6k - 1` and `6k + 1`) starting from `i` and stepping by `6` up to `limit`.
-/
def checkDivisors (n : Nat) (i : Nat) (limit : Nat) : Bool :=
  if _ : i ≤ limit then
    if n % i == 0 || n % (i + 2) == 0 then
      false
    else
      checkDivisors n (i + 6) limit
  else
    true
termination_by limit + 1 - i

/--
Check if a non-negative integer is prime.
A prime number is a natural number greater than 1 that is not divisible by any
positive integer other than 1 and itself.
-/
def is_prime (n : Int) : Bool :=
  if n ≤ 1 then
    false
  else if n ≤ 3 then
    true
  else if n % 2 == 0 || n % 3 == 0 then
    false
  else
    let natN := n.toNat
    checkDivisors natN 5 (Nat.sqrt natN)

/-! ## Unit Tests -/

-- Docstring examples
example : is_prime 2 = true := by native_decide
example : is_prime 4 = false := by native_decide
example : is_prime 0 = false := by native_decide

-- Test suite (`check`) examples and additional edge/composite/prime cases
example : is_prime 7 = true := by native_decide
example : is_prime 1 = false := by native_decide
example : is_prime (-1) = false := by native_decide
example : is_prime 3 = true := by native_decide
example : is_prime 5 = true := by native_decide
example : is_prime 9 = false := by native_decide
example : is_prime 25 = false := by native_decide
example : is_prime 29 = true := by native_decide
example : is_prime 35 = false := by native_decide
example : is_prime 49 = false := by native_decide
example : is_prime 97 = true := by native_decide
example : is_prime 121 = false := by native_decide

#eval is_prime 2
#eval is_prime 4
#eval is_prime 0
#eval is_prime 7
#eval is_prime 97

/-! ## Pre-condition -/

/--
Pre-condition for `is_prime`: the input integer `n` must be non-negative (`n ≥ 0`),
corresponding to `def pre(n: int) -> bool: return isinstance(n, int) and n >= 0`.
-/
def Pre (n : Int) : Prop :=
  0 ≤ n

/-! ## Property Propositions and Theorems -/

/--
Characterization of `checkDivisors`: it returns `true` if and only if for every step `k`
with `i + 6 * k ≤ limit`, neither `i + 6 * k` nor `i + 6 * k + 2` divides `n`.
-/
theorem checkDivisors_eq_true_iff (n i limit : Nat) :
    checkDivisors n i limit = true ↔
      ∀ k : Nat, i + 6 * k ≤ limit → ¬(i + 6 * k ∣ n) ∧ ¬(i + 6 * k + 2 ∣ n) := by
  induction i using checkDivisors.induct n limit with
  | case1 i hi hdiv =>
    rw [checkDivisors]
    simp only [hi, ↓reduceDIte, hdiv, ↓reduceIte, Bool.false_eq_true, false_iff, not_forall, not_and]
    have hdiv' : n % i = 0 ∨ n % (i + 2) = 0 := by simpa using hdiv
    refine ⟨0, by omega, ?_⟩
    intro h1
    rcases hdiv' with h | h
    · exfalso; exact h1 (by simpa using Nat.dvd_of_mod_eq_zero h)
    · simpa using Nat.dvd_of_mod_eq_zero h
  | case2 i hi hdiv ih =>
    rw [checkDivisors]
    simp only [hi, ↓reduceDIte, hdiv, Bool.false_eq_true, ↓reduceIte]
    rw [ih]
    have hdiv' : ¬(i ∣ n) ∧ ¬(i + 2 ∣ n) := by
      simp [Nat.dvd_iff_mod_eq_zero] at hdiv ⊢
      exact hdiv
    constructor
    · intro hAll k hk
      cases k with
      | zero =>
        simpa using hdiv'
      | succ k' =>
        have hk' : (i + 6) + 6 * k' ≤ limit := by omega
        have hstep := hAll k' hk'
        have heq1 : (i + 6) + 6 * k' = i + 6 * (k' + 1) := by omega
        rw [← heq1]
        exact hstep
    · intro hAll k' hk'
      have hk : i + 6 * (k' + 1) ≤ limit := by omega
      have hstep := hAll (k' + 1) hk
      have heq1 : (i + 6) + 6 * k' = i + 6 * (k' + 1) := by omega
      rw [heq1]
      exact hstep
  | case3 i hi =>
    rw [checkDivisors]
    simp [hi]
    intro k hk
    omega

/--
Core equivalence theorem: `is_prime n = true` if and only if `0 ≤ n` and `n.toNat` is prime.
-/
theorem is_prime_eq_true_iff_nat_prime (n : Int) :
    is_prime n = true ↔ (0 ≤ n ∧ Nat.Prime n.toNat) := by
  unfold is_prime
  by_cases h1 : n ≤ 1
  · simp [h1]
    intro _ hp
    have : n.toNat ≤ 1 := by omega
    have := hp.two_le
    omega
  · by_cases h3 : n ≤ 3
    · simp only [h1, ↓reduceIte, h3, true_iff]
      refine ⟨by omega, ?_⟩
      have : n.toNat = 2 ∨ n.toNat = 3 := by omega
      rcases this with h | h <;> rw [h]
      · exact Nat.prime_two
      · exact Nat.prime_three
    · simp only [h1, ↓reduceIte, h3]
      by_cases h23 : (n % 2 == 0 || n % 3 == 0) = true
      · simp only [h23, ↓reduceIte, Bool.false_eq_true, false_iff, not_and]
        intro _ hp
        have hdiv : n.toNat % 2 = 0 ∨ n.toNat % 3 = 0 := by
          simp [Bool.or_eq_true, beq_iff_eq] at h23
          omega
        rcases hdiv with h2 | h3'
        · have hdvd : 2 ∣ n.toNat := Nat.dvd_of_mod_eq_zero h2
          rcases (Nat.dvd_prime hp).mp hdvd with h | h <;> omega
        · have hdvd : 3 ∣ n.toNat := Nat.dvd_of_mod_eq_zero h3'
          rcases (Nat.dvd_prime hp).mp hdvd with h | h <;> omega
      · simp only [h23, Bool.false_eq_true, ↓reduceIte]
        rw [checkDivisors_eq_true_iff]
        have hn4 : 4 ≤ n.toNat := by omega
        have hn0 : 0 ≤ n := by omega
        have hnot23 : ¬(2 ∣ n.toNat) ∧ ¬(3 ∣ n.toNat) := by
          simp [Bool.or_eq_true, beq_iff_eq] at h23
          rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
          omega
        constructor
        · intro hAll
          refine ⟨hn0, ?_⟩
          by_contra hnp
          have hpos : 0 < n.toNat := by omega
          have hne1 : n.toNat ≠ 1 := by omega
          have hp_prime : Nat.Prime n.toNat.minFac := Nat.minFac_prime hne1
          have hp_dvd : n.toNat.minFac ∣ n.toNat := Nat.minFac_dvd n.toNat
          have hp_sq : n.toNat.minFac ^ 2 ≤ n.toNat := Nat.minFac_sq_le_self hpos hnp
          have hp_le_sqrt : n.toNat.minFac ≤ Nat.sqrt n.toNat := by
            rw [Nat.le_sqrt]
            simpa [sq] using hp_sq
          have hp2 : 2 ≤ n.toNat.minFac := hp_prime.two_le
          have hp_not2 : ¬(2 ∣ n.toNat.minFac) := fun hd => hnot23.1 (dvd_trans hd hp_dvd)
          have hp_not3 : ¬(3 ∣ n.toNat.minFac) := fun hd => hnot23.2 (dvd_trans hd hp_dvd)
          have hp5 : 5 ≤ n.toNat.minFac := by omega
          let k := (n.toNat.minFac - 5) / 6
          have hm2 : (n.toNat.minFac - 5) % 2 = 0 := by omega
          have hm3 : (n.toNat.minFac - 5) % 3 ≠ 1 := by omega
          have hform : n.toNat.minFac = 5 + 6 * k ∨ n.toNat.minFac = 5 + 6 * k + 2 := by omega
          have hk_le : 5 + 6 * k ≤ Nat.sqrt n.toNat := by omega
          have hstep := hAll k hk_le
          rcases hform with h5 | h7
          · rw [← h5] at hstep
            exact hstep.1 hp_dvd
          · rw [← h7] at hstep
            exact hstep.2 hp_dvd
        · rintro ⟨_, hp⟩ k hk
          have hsq : (5 + 6 * k) * (5 + 6 * k) ≤ n.toNat := Nat.le_sqrt.mp hk
          constructor
          · intro hdvd
            rcases (Nat.dvd_prime hp).mp hdvd with h | h <;> nlinarith
          · intro hdvd
            rcases (Nat.dvd_prime hp).mp hdvd with h | h <;> nlinarith

/--
Property 1: Numbers less than or equal to `1` (including `0` and `1`) are not prime.
-/
def le_one_not_prime_prop (n : Int) : Prop :=
  n ≤ 1 → is_prime n = false

/-- Theorem proving `le_one_not_prime_prop` under `Pre`. -/
theorem le_one_not_prime_thm (n : Int) : Pre n → le_one_not_prime_prop n := by
  intro _ h1
  unfold is_prime
  simp [h1]

/--
Property 2: The small integers `2` and `3` are prime.
-/
def small_primes_prop (n : Int) : Prop :=
  (n = 2 ∨ n = 3) → is_prime n = true

/-- Theorem proving `small_primes_prop` under `Pre`. -/
theorem small_primes_thm (n : Int) : Pre n → small_primes_prop n := by
  intro _ h23
  unfold is_prime
  rcases h23 with rfl | rfl <;> simp

/--
Property 3: Any integer greater than `3` that is divisible by `2` or `3` is not prime.
-/
def div_two_or_three_not_prime_prop (n : Int) : Prop :=
  n > 3 → (n % 2 = 0 ∨ n % 3 = 0) → is_prime n = false

/-- Theorem proving `div_two_or_three_not_prime_prop` under `Pre`. -/
theorem div_two_or_three_not_prime_thm (n : Int) : Pre n → div_two_or_three_not_prime_prop n := by
  intro _ hgt3 hdiv
  unfold is_prime
  have hnot1 : ¬(n ≤ 1) := by omega
  have hnot3 : ¬(n ≤ 3) := by omega
  have hcond : (n % 2 == 0 || n % 3 == 0) = true := by
    simp only [Bool.or_eq_true, beq_iff_eq]
    exact hdiv
  simp [hnot1, hnot3, hcond]

/--
Property 4: Docstring primality specification — `is_prime n = true` if and only if
`n > 1` and `n` is not divisible by any integer `d` with `1 < d < n`.
-/
def prime_divisibility_prop (n : Int) : Prop :=
  is_prime n = true ↔ (1 < n ∧ ∀ d : Int, 1 < d → d < n → ¬(d ∣ n))

/-- Theorem proving `prime_divisibility_prop` under `Pre`. -/
theorem prime_divisibility_thm (n : Int) : Pre n → prime_divisibility_prop n := by
  intro _
  unfold prime_divisibility_prop
  rw [is_prime_eq_true_iff_nat_prime, Nat.prime_def_lt']
  constructor
  · rintro ⟨hn0, hn2, hdiv⟩
    refine ⟨by omega, ?_⟩
    intro d hd1 hdn hdvd
    have hd_nonneg : 0 ≤ d := by omega
    have hd_nat : (d.toNat : Int) = d := Int.toNat_of_nonneg hd_nonneg
    have hn_nat : (n.toNat : Int) = n := Int.toNat_of_nonneg hn0
    have hdvd_nat : d.toNat ∣ n.toNat := by
      rw [← Int.ofNat_dvd, hd_nat, hn_nat]
      exact hdvd
    exact hdiv d.toNat (by omega) (by omega) hdvd_nat
  · rintro ⟨hn1, hdiv⟩
    have hn0 : 0 ≤ n := by omega
    refine ⟨hn0, by omega, ?_⟩
    intro m hm2 hmn hdvd
    have hdvd_int : (m : Int) ∣ n := by
      have hn_nat : (n.toNat : Int) = n := Int.toNat_of_nonneg hn0
      rw [← hn_nat]
      exact Int.ofNat_dvd.mpr hdvd
    exact hdiv (m : Int) (by omega) (by omega) hdvd_int

/--
Property 5: Equivalence with Mathlib's `Nat.Prime` predicate on `n.toNat`.
-/
def nat_prime_iff_prop (n : Int) : Prop :=
  is_prime n = true ↔ (0 ≤ n ∧ Nat.Prime n.toNat)

/-- Theorem proving `nat_prime_iff_prop` under `Pre`. -/
theorem nat_prime_iff_thm (n : Int) : Pre n → nat_prime_iff_prop n := by
  intro _
  exact is_prime_eq_true_iff_nat_prime n

/-! ## Post-condition -/

/--
Full post-condition for `is_prime` as the conjunction of all stated properties.
-/
def Post_prop (n : Int) : Prop :=
  le_one_not_prime_prop n ∧
  small_primes_prop n ∧
  div_two_or_three_not_prime_prop n ∧
  prime_divisibility_prop n ∧
  nat_prime_iff_prop n

/-! ## Property-Based Tests (PBTs) -/

-- Randomized PBTs for each property and the post-condition
#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n →
  (!decide (n ≤ 1) || is_prime n == false) = true) { numRetries := 50 }

#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n →
  (!decide (n = 2 ∨ n = 3) || is_prime n == true) = true) { numRetries := 50 }

#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n →
  (!decide (n > 3 ∧ (n % 2 = 0 ∨ n % 3 = 0)) || is_prime n == false) = true) { numRetries := 50 }

#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n →
  (is_prime n == decide (1 < n ∧ ((List.range n.toNat).filter (· ≥ 2)).all (fun d => !(d ∣ n.toNat)))) = true) { numRetries := 50 }

#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n →
  (is_prime n == decide (0 ≤ n ∧ Nat.Prime n.toNat)) = true) { numRetries := 50 }

#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n →
  ((!decide (n ≤ 1) || is_prime n == false) &&
   (!decide (n = 2 ∨ n = 3) || is_prime n == true) &&
   (!decide (n > 3 ∧ (n % 2 = 0 ∨ n % 3 = 0)) || is_prime n == false) &&
   (is_prime n == decide (1 < n ∧ ((List.range n.toNat).filter (· ≥ 2)).all (fun d => !(d ∣ n.toNat)))) &&
   (is_prime n == decide (0 ≤ n ∧ Nat.Prime n.toNat))) = true) { numRetries := 50 }

-- Bounded exhaustive PBTs over [0, 200) for each property and the post-condition
example : (List.range 200).all (fun m =>
  let n : Int := m
  (!decide (n ≤ 1) || is_prime n == false)) = true := by native_decide

example : (List.range 200).all (fun m =>
  let n : Int := m
  (!decide (n = 2 ∨ n = 3) || is_prime n == true)) = true := by native_decide

example : (List.range 200).all (fun m =>
  let n : Int := m
  (!decide (n > 3 ∧ (n % 2 = 0 ∨ n % 3 = 0)) || is_prime n == false)) = true := by native_decide

example : (List.range 200).all (fun m =>
  let n : Int := m
  is_prime n == decide (1 < n ∧ ((List.range n.toNat).filter (· ≥ 2)).all (fun d => !(d ∣ n.toNat)))) = true := by native_decide

example : (List.range 200).all (fun m =>
  let n : Int := m
  is_prime n == decide (0 ≤ n ∧ Nat.Prime n.toNat)) = true := by native_decide

example : (List.range 200).all (fun m =>
  let n : Int := m
  (!decide (n ≤ 1) || is_prime n == false) &&
  (!decide (n = 2 ∨ n = 3) || is_prime n == true) &&
  (!decide (n > 3 ∧ (n % 2 = 0 ∨ n % 3 = 0)) || is_prime n == false) &&
  (is_prime n == decide (1 < n ∧ ((List.range n.toNat).filter (· ≥ 2)).all (fun d => !(d ∣ n.toNat)))) &&
  (is_prime n == decide (0 ≤ n ∧ Nat.Prime n.toNat))) = true := by native_decide

/-! ## Correctness Theorem (Pre -> Post) -/

/--
Main correctness theorem: for any integer `n` satisfying `Pre n`, `Post_prop n` holds.
-/
theorem is_prime_correct (n : Int) : Pre n → Post_prop n := by
  intro hpre
  exact ⟨le_one_not_prime_thm n hpre,
         small_primes_thm n hpre,
         div_two_or_three_not_prime_thm n hpre,
         prime_divisibility_thm n hpre,
         nat_prime_iff_thm n hpre⟩

/-! ## Imperative Implementation -/

/--
Imperative implementation of `is_prime` using `Id.run do` and mutable loop state,
following the Python `for i in range(5, int(math.sqrt(n)) + 1, 6)` loop.
-/
def is_prime_imp (n : Int) : Bool := Id.run do
  if n ≤ 1 then
    return false
  if n ≤ 3 then
    return true
  if n % 2 == 0 || n % 3 == 0 then
    return false
  let natN := n.toNat
  let limit := Nat.sqrt natN
  let mut i := 5
  let mut isPrime := true
  for _ in List.range (limit + 1) do
    if i ≤ limit then
      if natN % i == 0 || natN % (i + 2) == 0 then
        isPrime := false
        break
      i := i + 6
  return isPrime

/-! ## Imperative Tests -/

example : is_prime_imp 2 = true := by native_decide
example : is_prime_imp 4 = false := by native_decide
example : is_prime_imp 0 = false := by native_decide
example : is_prime_imp 7 = true := by native_decide
example : is_prime_imp 1 = false := by native_decide
example : is_prime_imp (-1) = false := by native_decide
example : is_prime_imp 3 = true := by native_decide
example : is_prime_imp 5 = true := by native_decide
example : is_prime_imp 9 = false := by native_decide
example : is_prime_imp 25 = false := by native_decide
example : is_prime_imp 29 = true := by native_decide
example : is_prime_imp 35 = false := by native_decide
example : is_prime_imp 49 = false := by native_decide
example : is_prime_imp 97 = true := by native_decide
example : is_prime_imp 121 = false := by native_decide

#eval is_prime_imp 2
#eval is_prime_imp 4
#eval is_prime_imp 0
#eval is_prime_imp 7
#eval is_prime_imp 97

/-! ## Equivalence Theorem (Functional = Imperative) -/

/--
Helper lemma proving that the imperative `for` loop in `is_prime_imp` computes the
same result as the recursive `checkDivisors` function whenever `limit + 1 - i ≤ xs.length`.
-/
theorem loop_eq_checkDivisors (natN limit : Nat) (xs : List Nat) (i : Nat)
    (h : limit + 1 - i ≤ xs.length) :
    (Id.run do
      let mut i := i
      let mut isPrime := true
      for _ in xs do
        if i ≤ limit then
          if natN % i == 0 || natN % (i + 2) == 0 then
            isPrime := false
            break
          i := i + 6
      return isPrime) = checkDivisors natN i limit := by
  induction xs generalizing i with
  | nil =>
    simp at h
    unfold checkDivisors
    have : ¬ (i ≤ limit) := by omega
    simp [this]
  | cons x xs ih =>
    by_cases hi : i ≤ limit
    · by_cases hdiv : natN % i = 0 ∨ natN % (i + 2) = 0
      · rw [checkDivisors]
        simp [hi, hdiv]
      · have hlen : limit + 1 - (i + 6) ≤ xs.length := by
          simp at h
          omega
        have ih' := ih (i + 6) hlen
        rw [checkDivisors]
        simp [hi, hdiv] at ih' ⊢
        exact ih'
    · have ih' := ih i (by omega)
      simp [hi] at ih' ⊢
      exact ih'

/--
Equivalence theorem showing that the functional implementation `is_prime` and the
imperative implementation `is_prime_imp` agree on all integer inputs `n`.
-/
theorem is_prime_eq_is_prime_imp (n : Int) : is_prime n = is_prime_imp n := by
  unfold is_prime is_prime_imp
  by_cases h1 : n ≤ 1
  · simp [h1]
  · by_cases h3 : n ≤ 3
    · simp [h1, h3]
    · by_cases h2 : 2 ∣ n
      · simp [h1, h3, h2]
      · by_cases h3' : 3 ∣ n
        · simp [h1, h3, h2, h3']
        · have hloop := loop_eq_checkDivisors n.toNat (Nat.sqrt n.toNat)
            (List.range (Nat.sqrt n.toNat + 1)) 5 (by simp; omega)
          simp [h1, h3, h2, h3'] at hloop ⊢
          exact hloop.symm

end «23_is_prime»
