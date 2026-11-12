import Mathlib

/-!
# `is_prime` -- primality test for non-negative integers

Lean 4 translation of the Python program `23_is_prime.py`.

The Python function `is_prime(n)`:
* raises `ValueError` when the precondition `n >= 0` fails;
* returns `False` for `n <= 1`, `True` for `n` in `{2, 3}`;
* returns `False` when `n` is divisible by `2` or by `3`;
* otherwise performs trial division by `i` and `i + 2` for
  `i in range(5, int(math.sqrt(n)) + 1, 6)` (all `6k ± 1` candidates up to `⌊√n⌋`)
  and returns `False` as soon as a divisor is found, `True` otherwise.

Modelling choices:
* the result type is `Except String Bool`; `Except.error` models the `ValueError`;
* `int(math.sqrt(n))` is modelled by the exact integer square root `Nat.sqrt`
  (the mathematical intent of the Python program);
* Python's `range(5, isqrt(n) + 1, 6)` is modelled by `List.range' 5 count 6`
  (functional version) and by the range `[5 : isqrt(n) + 1 : 6]` (imperative version).
-/

namespace «23_is_prime»

/-! ## Functional implementation -/

/-- Number of elements of Python's `range(5, s + 1, 6)`. -/
def rangeCount (s : Nat) : Nat := if 5 ≤ s then (s - 5) / 6 + 1 else 0

/-- The trial-division candidates `range(5, s + 1, 6) = [5, 11, 17, …]` (all `≤ s`). -/
def candidates (s : Nat) : List Nat := List.range' 5 (rangeCount s) 6

/-- Body of the Python function (after the precondition check), on natural numbers. -/
def isPrimeNat (n : Nat) : Bool :=
  if n ≤ 1 then false
  else if n ≤ 3 then true
  else if n % 2 == 0 || n % 3 == 0 then false
  else (candidates (Nat.sqrt n)).all fun i => !(n % i == 0 || n % (i + 2) == 0)

/-- The Python function `is_prime`.  `Except.error` models the `ValueError` raised
when the precondition `n >= 0` is violated. -/
def isPrime (n : Int) : Except String Bool :=
  if n < 0 then .error "Input must be non-negative integer"
  else .ok (isPrimeNat n.toNat)

/-! ## Unit tests -/

deriving instance DecidableEq for Except

-- doctests
example : isPrime 2 = .ok true := by native_decide
example : isPrime 4 = .ok false := by native_decide
example : isPrime 0 = .ok false := by native_decide
-- `check`
example : isPrime 7 = .ok true := by native_decide
example : isPrime (-1) = .error "Input must be non-negative integer" := by native_decide
example : isPrime (-100) = .error "Input must be non-negative integer" := by native_decide
-- more
example : isPrime 1 = .ok false := by native_decide
example : isPrime 3 = .ok true := by native_decide
example : isPrime 9 = .ok false := by native_decide
example : isPrime 25 = .ok false := by native_decide
example : isPrime 49 = .ok false := by native_decide
example : isPrime 97 = .ok true := by native_decide
example : isPrime 1000003 = .ok true := by native_decide
example : isPrime 1000001 = .ok false := by native_decide

#eval isPrime 7
#eval isPrime 0
#eval isPrime (-1)
#eval (List.range 40).filter (fun n => isPrimeNat n)

/-! ## Pre-condition -/

/-- Python `pre(n)`: `n` is a (non-negative) integer. -/
def Pre (n : Int) : Prop := 0 ≤ n

/-! ## Auxiliary lemmas about the candidate list -/

theorem mem_candidates {s i : Nat} : i ∈ candidates s ↔ 5 ≤ i ∧ i ≤ s ∧ i % 6 = 5 := by
  unfold candidates rangeCount
  simp only [List.mem_range']
  constructor
  · rintro ⟨k, hk, rfl⟩
    split_ifs at hk <;> omega
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(i - 5) / 6, ?_, ?_⟩
    · split_ifs <;> omega
    · omega

/-- The core correctness statement on natural numbers: the `6k ± 1` trial division
decides primality. -/
theorem isPrimeNat_iff (n : Nat) : isPrimeNat n = true ↔ Nat.Prime n := by
  unfold isPrimeNat
  split_ifs with h1 h2 h3
  · simp only [false_iff]
    intro hp
    have := hp.two_le
    omega
  · simp only [true_iff]
    rcases (show n = 2 ∨ n = 3 by omega) with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  · simp only [false_iff]
    intro hp
    simp only [Bool.or_eq_true, beq_iff_eq] at h3
    rcases h3 with h | h
    · have hd : 2 ∣ n := Nat.dvd_of_mod_eq_zero h
      rcases (Nat.dvd_prime hp).mp hd with h' | h' <;> omega
    · have hd : 3 ∣ n := Nat.dvd_of_mod_eq_zero h
      rcases (Nat.dvd_prime hp).mp hd with h' | h' <;> omega
  · simp only [Bool.or_eq_true, beq_iff_eq, not_or] at h3
    obtain ⟨h2', h3'⟩ := h3
    simp only [List.all_eq_true, mem_candidates, Bool.not_eq_true', Bool.or_eq_false_iff,
      beq_eq_false_iff_ne, ne_eq]
    constructor
    · intro hall
      rw [Nat.prime_def_le_sqrt]
      refine ⟨by omega, ?_⟩
      intro m hm2 hms hdvd
      have hmod := Nat.mod_eq_zero_of_dvd hdvd
      have hcases : m % 6 = 0 ∨ m % 6 = 1 ∨ m % 6 = 2 ∨ m % 6 = 3 ∨ m % 6 = 4 ∨ m % 6 = 5 := by
        omega
      rcases hcases with h | h | h | h | h | h
      · apply h2'
        have h2m : 2 ∣ m := by omega
        exact Nat.mod_eq_zero_of_dvd (h2m.trans hdvd)
      · have hi := hall (m - 2) ⟨by omega, by omega, by omega⟩
        have heq : m - 2 + 2 = m := by omega
        rw [heq] at hi
        exact hi.2 hmod
      · apply h2'
        have h2m : 2 ∣ m := by omega
        exact Nat.mod_eq_zero_of_dvd (h2m.trans hdvd)
      · apply h3'
        have h3m : 3 ∣ m := by omega
        exact Nat.mod_eq_zero_of_dvd (h3m.trans hdvd)
      · apply h2'
        have h2m : 2 ∣ m := by omega
        exact Nat.mod_eq_zero_of_dvd (h2m.trans hdvd)
      · have hi := hall m ⟨by omega, hms, h⟩
        exact hi.1 hmod
    · rintro hp i ⟨hi5, his, -⟩
      have hii : i * i ≤ n := Nat.le_sqrt.mp his
      have h5i : i * 5 ≤ i * i := Nat.mul_le_mul_left i hi5
      constructor
      · intro hmod
        have hd := Nat.dvd_of_mod_eq_zero hmod
        rcases (Nat.dvd_prime hp).mp hd with h | h
        · omega
        · subst h
          omega
      · intro hmod
        have hd := Nat.dvd_of_mod_eq_zero hmod
        rcases (Nat.dvd_prime hp).mp hd with h | h
        · omega
        · omega

/-! ## Properties -/

/-- Property 1: on admissible inputs the answer is `True` exactly when `n` is prime. -/
def isPrime_prime_prop (n : Int) : Prop :=
  isPrime n = .ok true ↔ Nat.Prime n.toNat

theorem isPrime_prime_thm (n : Int) (h : Pre n) : isPrime_prime_prop n := by
  unfold isPrime_prime_prop isPrime
  rw [if_neg (not_lt.mpr h)]
  simp only [Except.ok.injEq]
  exact isPrimeNat_iff _

/-- Property 2: on admissible inputs the answer is `False` exactly when `n` is not prime. -/
def isPrime_not_prime_prop (n : Int) : Prop :=
  isPrime n = .ok false ↔ ¬ Nat.Prime n.toNat

theorem isPrime_not_prime_thm (n : Int) (h : Pre n) : isPrime_not_prime_prop n := by
  unfold isPrime_not_prime_prop isPrime
  rw [if_neg (not_lt.mpr h)]
  simp only [Except.ok.injEq]
  rw [← isPrimeNat_iff, Bool.not_eq_true]

/-- Property 3 (the docstring definition of primality, stated on integers): the answer is
`True` iff `n > 1` and the only positive divisors of `n` are `1` and `n`. -/
def isPrime_divisors_prop (n : Int) : Prop :=
  isPrime n = .ok true ↔ (1 < n ∧ ∀ d : Int, 0 < d → d ∣ n → d = 1 ∨ d = n)

theorem isPrime_divisors_thm (n : Int) (h : Pre n) : isPrime_divisors_prop n := by
  unfold isPrime_divisors_prop
  have hp : isPrime n = .ok true ↔ Nat.Prime n.toNat := isPrime_prime_thm n h
  rw [hp]
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
  simp only [Int.toNat_natCast]
  constructor
  · intro hpm
    refine ⟨by exact_mod_cast hpm.one_lt, ?_⟩
    intro d hd hdvd
    obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le hd.le
    have hd' : d ∣ m := Int.natCast_dvd_natCast.mp hdvd
    rcases (Nat.dvd_prime hpm).mp hd' with h' | h' <;> omega
  · rintro ⟨h1, hdiv⟩
    rw [Nat.prime_def]
    refine ⟨by omega, ?_⟩
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
    have := hdiv d (by exact_mod_cast hd0) (Int.natCast_dvd_natCast.mpr hd)
    omega

/-- Property 4: the function returns normally (no exception) exactly on admissible inputs. -/
def isPrime_ok_iff_prop (n : Int) : Prop :=
  (∃ b, isPrime n = .ok b) ↔ Pre n

theorem isPrime_ok_iff_thm (n : Int) : isPrime_ok_iff_prop n := by
  unfold isPrime_ok_iff_prop isPrime Pre
  constructor
  · rintro ⟨b, hb⟩
    by_contra hneg
    rw [if_pos (by omega)] at hb
    exact Except.noConfusion hb
  · intro h
    exact ⟨_, if_neg (not_lt.mpr h)⟩

/-- Property 5: negative inputs raise `ValueError` (modelled by `Except.error`). -/
def isPrime_neg_prop (n : Int) : Prop :=
  n < 0 → isPrime n = .error "Input must be non-negative integer"

theorem isPrime_neg_thm (n : Int) : isPrime_neg_prop n := by
  intro h
  unfold isPrime
  rw [if_pos h]

/-- Property 6: `0` and `1` are not prime. -/
def isPrime_le_one_prop (n : Int) : Prop :=
  n ≤ 1 → isPrime n = .ok false

theorem isPrime_le_one_thm (n : Int) (h : Pre n) : isPrime_le_one_prop n := by
  intro hle
  have hnp : isPrime n = .ok false ↔ ¬ Nat.Prime n.toNat := isPrime_not_prime_thm n h
  rw [hnp]
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
  rw [Int.toNat_natCast]
  intro hp
  have := hp.two_le
  omega

/-- Property 7: `2` and `3` are prime. -/
def isPrime_two_three_prop (n : Int) : Prop :=
  (n = 2 ∨ n = 3) → isPrime n = .ok true

theorem isPrime_two_three_thm (n : Int) (h : Pre n) : isPrime_two_three_prop n := by
  intro h23
  have hp : isPrime n = .ok true ↔ Nat.Prime n.toNat := isPrime_prime_thm n h
  rw [hp]
  rcases h23 with rfl | rfl
  · exact Nat.prime_two
  · exact Nat.prime_three

/-- Property 8: numbers `≥ 4` divisible by `2` or `3` are rejected. -/
def isPrime_small_factor_prop (n : Int) : Prop :=
  4 ≤ n → (2 ∣ n ∨ 3 ∣ n) → isPrime n = .ok false

theorem isPrime_small_factor_thm (n : Int) (h : Pre n) : isPrime_small_factor_prop n := by
  intro h4 hdiv
  have hnp : isPrime n = .ok false ↔ ¬ Nat.Prime n.toNat := isPrime_not_prime_thm n h
  rw [hnp]
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
  rw [Int.toNat_natCast]
  intro hp
  rcases hdiv with hd | hd
  · have hd' : 2 ∣ m := by exact_mod_cast hd
    rcases (Nat.dvd_prime hp).mp hd' with h' | h' <;> omega
  · have hd' : 3 ∣ m := by exact_mod_cast hd
    rcases (Nat.dvd_prime hp).mp hd' with h' | h' <;> omega

/-- Property 9: on admissible inputs the answer is `True` exactly when `n` is a prime
integer in the sense of Mathlib's `Prime` (on `ℤ`). -/
def isPrime_int_prime_prop (n : Int) : Prop :=
  isPrime n = .ok true ↔ Prime n

theorem isPrime_int_prime_thm (n : Int) (h : Pre n) : isPrime_int_prime_prop n := by
  unfold isPrime_int_prime_prop
  have hp : isPrime n = .ok true ↔ Nat.Prime n.toNat := isPrime_prime_thm n h
  rw [hp, Int.prime_iff_natAbs_prime]
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
  simp

/-! ## Post-condition -/

/-- Post-condition: conjunction of all properties of `isPrime n`. -/
def Post_prop (n : Int) : Prop :=
  isPrime_prime_prop n ∧ isPrime_not_prime_prop n ∧ isPrime_divisors_prop n ∧
    isPrime_ok_iff_prop n ∧ isPrime_neg_prop n ∧ isPrime_le_one_prop n ∧
    isPrime_two_three_prop n ∧ isPrime_small_factor_prop n ∧ isPrime_int_prime_prop n

/-! ## Property-based tests -/

-- Property 1 (randomized over the admissible domain, and bounded exhaustive)
#eval Plausible.Testable.check
  (∀ k : Nat, isPrime k = .ok true ↔ Nat.Prime (k : Int).toNat)
example : (List.range 600).all (fun n => isPrimeNat n == decide (Nat.Prime n)) = true := by
  native_decide
example : (List.range 600).all
    (fun n => decide (isPrime n = .ok true ↔ Nat.Prime (n : Int).toNat)) = true := by
  native_decide
-- Property 2
#eval Plausible.Testable.check
  (∀ k : Nat, isPrime k = .ok false ↔ ¬ Nat.Prime (k : Int).toNat)
example : (List.range 600).all
    (fun n => decide (isPrime n = .ok false ↔ ¬ Nat.Prime (n : Int).toNat)) = true := by
  native_decide
-- Property 3 (bounded: all divisors `0 < d ≤ n` are checked exhaustively)
example : ∀ n ∈ List.range 400, (isPrime n = .ok true ↔
    (1 < (n : Int) ∧ ∀ d ∈ List.range (n + 1), 0 < d → d ∣ n → d = 1 ∨ d = n)) := by
  native_decide
-- Property 4 (ok iff Pre)
#eval Plausible.Testable.check
  (∀ n : Int, (∃ b, isPrime n = .ok b) ↔ 0 ≤ n)
example : (List.range 300).all (fun k =>
    let n : Int := (k : Int) - 100
    decide ((∃ b, isPrime n = .ok b) ↔ 0 ≤ n)) = true := by
  native_decide
-- Property 5 (negative inputs raise)
#eval Plausible.Testable.check
  (∀ k : Nat, isPrime (-(k : Int) - 1) = .error "Input must be non-negative integer")
example : (List.range 100).all
    (fun k => isPrime (-(k : Int) - 1) == .error "Input must be non-negative integer") = true := by
  native_decide
-- Property 6 and 7
example : (List.range 2).all (fun n => isPrime n == .ok false) = true := by native_decide
example : ([2, 3] : List Int).all (fun n => isPrime n == .ok true) = true := by native_decide
-- Property 8 (every `n ≥ 4` with `2 ∣ n` is `2k + 4`; with `3 ∣ n` is `3k + 6`)
#eval Plausible.Testable.check
  (∀ k : Nat, isPrime (2 * (k : Int) + 4) = .ok false)
#eval Plausible.Testable.check
  (∀ k : Nat, isPrime (3 * (k : Int) + 6) = .ok false)
example : (List.range 300).all (fun n =>
    decide (4 ≤ (n : Int) → (2 ∣ (n : Int) ∨ 3 ∣ (n : Int)) → isPrime n = .ok false)) = true := by
  native_decide
-- Property 9: `Prime (n : Int)` has no `Decidable` instance, so it is tested through its
-- executable counterpart `Nat.Prime n.natAbs` (`Int.prime_iff_natAbs_prime`).
#eval Plausible.Testable.check
  (∀ k : Nat, isPrime k = .ok true ↔ Nat.Prime (k : Int).natAbs)
example : (List.range 600).all
    (fun n => decide (isPrime n = .ok true ↔ Nat.Prime (n : Int).natAbs)) = true := by
  native_decide
-- Post-condition (bounded, inputs `-100 ≤ n < 200`; property 9 via `Nat.Prime n.natAbs`)
example : (List.range 300).all (fun k =>
    let n : Int := (k : Int) - 100
    decide ((0 ≤ n → (isPrime n = .ok true ↔ Nat.Prime n.toNat)) ∧
      (0 ≤ n → (isPrime n = .ok false ↔ ¬ Nat.Prime n.toNat)) ∧
      ((∃ b, isPrime n = .ok b) ↔ 0 ≤ n) ∧
      (n < 0 → isPrime n = .error "Input must be non-negative integer") ∧
      (0 ≤ n → n ≤ 1 → isPrime n = .ok false) ∧
      ((n = 2 ∨ n = 3) → isPrime n = .ok true) ∧
      (4 ≤ n → (2 ∣ n ∨ 3 ∣ n) → isPrime n = .ok false) ∧
      (0 ≤ n → (isPrime n = .ok true ↔ Nat.Prime n.natAbs)))) = true := by
  native_decide

/-! ## Correctness theorem -/

theorem isPrime_correct (n : Int) (h : Pre n) : Post_prop n :=
  ⟨isPrime_prime_thm n h, isPrime_not_prime_thm n h, isPrime_divisors_thm n h,
    isPrime_ok_iff_thm n, isPrime_neg_thm n, isPrime_le_one_thm n h,
    isPrime_two_three_thm n h, isPrime_small_factor_thm n h, isPrime_int_prime_thm n h⟩

/-! ## Imperative implementation -/

/-- Imperative version of the Python body: early returns, a `for` loop over
`range(5, isqrt(n) + 1, 6)` with a mutable result and `break` on the first divisor. -/
def isPrimeNatImp (n : Nat) : Bool := Id.run do
  if n ≤ 1 then return false
  if n ≤ 3 then return true
  if n % 2 == 0 || n % 3 == 0 then return false
  let s := Nat.sqrt n
  let mut result := true
  for i in [5 : s + 1 : 6] do
    if n % i == 0 || n % (i + 2) == 0 then
      result := false
      break
  return result

/-- Imperative version of `is_prime`, raising (`throw`) on negative inputs. -/
def isPrimeImp (n : Int) : Except String Bool := do
  if n < 0 then throw "Input must be non-negative integer"
  return isPrimeNatImp n.toNat

/-! ## Imperative tests -/

example : isPrimeImp 2 = .ok true := by native_decide
example : isPrimeImp 4 = .ok false := by native_decide
example : isPrimeImp 0 = .ok false := by native_decide
example : isPrimeImp 7 = .ok true := by native_decide
example : isPrimeImp (-1) = .error "Input must be non-negative integer" := by native_decide
example : isPrimeImp 25 = .ok false := by native_decide
example : isPrimeImp 97 = .ok true := by native_decide
example : isPrimeImp 1000003 = .ok true := by native_decide
example : (List.range 600).all (fun n => isPrimeNatImp n == isPrimeNat n) = true := by
  native_decide
#eval Plausible.Testable.check (∀ n : Int, isPrimeImp n = isPrime n)
#eval isPrimeImp 7
#eval isPrimeImp (-1)

/-! ## Equivalence functional = imperative -/

/-- The `for … break` loop over a list computes `List.all`. -/
theorem forIn_break_eq (n : Nat) (l : List Nat) :
    (Id.run do
      let mut result := true
      for i in l do
        if n % i == 0 || n % (i + 2) == 0 then
          result := false
          break
      return result) = l.all (fun i => !(n % i == 0 || n % (i + 2) == 0)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : n % a = 0 ∨ n % (a + 2) = 0
    · rcases h with h | h <;> simp [h]
    · rw [not_or] at h
      obtain ⟨h1, h2⟩ := h
      have hb1 : (n % a == 0) = false := beq_eq_false_iff_ne.mpr h1
      have hb2 : (n % (a + 2) == 0) = false := beq_eq_false_iff_ne.mpr h2
      simp [h1, h2, hb1, hb2] at ih ⊢
      exact ih

/-- The Lean range `[5 : s + 1 : 6]` has as many elements as Python's `range(5, s + 1, 6)`. -/
theorem range_size (s : Nat) : ([5 : s + 1 : 6] : Std.Range).size = rangeCount s := by
  simp only [Std.Range.size, rangeCount]
  split_ifs <;> omega

theorem isPrimeNatImp_eq (n : Nat) : isPrimeNatImp n = isPrimeNat n := by
  unfold isPrimeNatImp isPrimeNat
  split_ifs with h1 h2 h3 <;> try rfl
  simp only [pure_bind]
  rw [Std.Range.forIn_eq_forIn_range', range_size]
  exact forIn_break_eq n _

/-- Functional and imperative versions of `is_prime` agree on every input
(including the exceptional negative inputs). -/
theorem isPrimeImp_eq (n : Int) : isPrimeImp n = isPrime n := by
  unfold isPrimeImp isPrime
  split_ifs with h
  · rfl
  · rw [isPrimeNatImp_eq]
    rfl

end «23_is_prime»
