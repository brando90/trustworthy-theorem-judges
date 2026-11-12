import Mathlib

/-!
# `is_prime`: primality test for a non-negative integer

Lean 4 formalization of the Python program `23_is_prime.py`.

* `is_prime(n)` raises `ValueError("Input must be non-negative integer")` for a
  negative `n`; this is modelled by the result type `Except String Bool`, with
  `.error "Input must be non-negative integer"` for the exceptional case.
* `0` and `1` are not prime, `2` and `3` are prime, multiples of `2` or `3`
  larger than `3` are not prime, and otherwise trial division by the numbers of
  the form `6k ± 1` (`i = 5, 11, 17, …` together with `i + 2`) up to `⌊√n⌋`
  decides primality — exactly as in the Python source.
* Python's `int(math.sqrt(n))` is modelled by the exact integer square root
  `Nat.sqrt n = ⌊√n⌋`, the mathematical intent of the program.
* The specification is Mathlib's `Nat.Prime`, together with the docstring's
  definition (a natural number greater than `1` whose only positive divisors are
  `1` and itself).
-/

namespace «23_is_prime»

-- Equality of `Except` results is decidable (needed for tests and PBTs).
deriving instance DecidableEq for Except

/-! ## Functional implementation -/

/-- The trial-division loop `for i in range(5, isqrt(n) + 1, 6)`: `i` is the
current candidate and the second argument is the number of remaining
iterations.  Returns `false` as soon as `i ∣ n` or `i + 2 ∣ n` (Python's early
`return False`), and `true` once the iterations are exhausted. -/
def trialLoop (n : Nat) : Nat → Nat → Bool
  | _, 0 => true
  | i, count + 1 =>
    if n % i = 0 ∨ n % (i + 2) = 0 then false
    else trialLoop n (i + 6) count

/-- Number of iterations of `range(5, isqrt(n) + 1, 6)`, i.e. the number of
`i ∈ {5, 11, 17, …}` with `i ≤ ⌊√n⌋`. -/
def loopCount (n : Nat) : Nat := (Nat.sqrt n + 1) / 6

/-- Primality test on natural numbers (the body of `is_prime` after the
pre-condition check). -/
def isPrimeNat (n : Nat) : Bool :=
  if n ≤ 1 then false
  else if n ≤ 3 then true
  else if n % 2 = 0 ∨ n % 3 = 0 then false
  else trialLoop n 5 (loopCount n)

/-- `is_prime(n)`: `.error` models the `ValueError` raised for a negative
input; otherwise `.ok` carries the Boolean answer. -/
def isPrime (n : Int) : Except String Bool :=
  if n < 0 then .error "Input must be non-negative integer"
  else .ok (isPrimeNat n.toNat)

/-! ## Unit tests (from the docstring and `check`) -/

example : isPrime 2 = .ok true := by native_decide
example : isPrime 4 = .ok false := by native_decide
example : isPrime 0 = .ok false := by native_decide
example : isPrime 7 = .ok true := by native_decide
example : isPrime 1 = .ok false := by native_decide
example : isPrime 3 = .ok true := by native_decide
example : isPrime 25 = .ok false := by native_decide
example : isPrime 49 = .ok false := by native_decide
example : isPrime 97 = .ok true := by native_decide
example : isPrime 7919 = .ok true := by native_decide
example : isPrime (-1) = .error "Input must be non-negative integer" := by native_decide

#eval isPrime 7      -- Except.ok true
#eval isPrime 0      -- Except.ok false
#eval isPrime (-1)   -- Except.error "Input must be non-negative integer"
#eval (List.range 50).filter (fun n => decide (isPrime n = .ok true))
-- [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

/-! ## Pre-condition -/

/-- `pre(n)`: the input is a non-negative integer. -/
def Pre (n : Int) : Prop := 0 ≤ n

/-! ## Properties -/

/-- On admissible inputs no exception is raised: the result is some `.ok b`. -/
def isPrime_ok_prop : Prop :=
  ∀ n : Int, 0 ≤ n → ∃ b : Bool, isPrime n = .ok b

/-- Main specification: on admissible inputs the answer is exactly Mathlib's
`Nat.Prime`. -/
def isPrime_eq_prime_prop : Prop :=
  ∀ n : Int, 0 ≤ n → isPrime n = .ok (decide (Nat.Prime n.toNat))

/-- The docstring's definition: the answer is `True` iff `n` is greater than
`1` and is not divisible by any positive integer other than `1` and itself. -/
def isPrime_true_iff_prop : Prop :=
  ∀ n : Int, 0 ≤ n →
    (isPrime n = .ok true ↔ 1 < n ∧ ∀ d : Int, 0 < d → d ∣ n → d = 1 ∨ d = n)

/-- The answer is `False` iff `n ≤ 1` or `n` has a divisor strictly between
`1` and `n`. -/
def isPrime_false_iff_prop : Prop :=
  ∀ n : Int, 0 ≤ n →
    (isPrime n = .ok false ↔ n ≤ 1 ∨ ∃ d : Int, 1 < d ∧ d < n ∧ d ∣ n)

/-- Edge cases of the docstring: `0` and `1` are not prime. -/
def isPrime_zero_one_prop : Prop :=
  isPrime 0 = .ok false ∧ isPrime 1 = .ok false

/-- Negative inputs are invalid and raise `ValueError`. -/
def isPrime_neg_prop : Prop :=
  ∀ n : Int, n < 0 → isPrime n = .error "Input must be non-negative integer"

/-! ### Auxiliary lemmas about the implementation -/

/-- Characterisation of the trial-division loop: it returns `true` iff none of
the `count` candidates `i, i + 6, i + 12, …` nor their successors `+ 2`
divide `n`. -/
theorem trialLoop_eq_true_iff (n i count : Nat) :
    trialLoop n i count = true ↔
      ∀ j < count, n % (i + 6 * j) ≠ 0 ∧ n % (i + 6 * j + 2) ≠ 0 := by
  induction count generalizing i with
  | zero => simp [trialLoop]
  | succ k ih =>
    simp only [trialLoop]
    by_cases h : n % i = 0 ∨ n % (i + 2) = 0
    · rw [if_pos h]
      simp only [Bool.false_eq_true, false_iff, not_forall]
      refine ⟨0, by omega, ?_⟩
      simp only [Nat.mul_zero, Nat.add_zero, ne_eq, not_and, not_not]
      intro h1
      exact h.resolve_left h1
    · rw [if_neg h, ih]
      constructor
      · intro H j hj
        rcases j with _ | j
        · simpa using h
        · have := H j (by omega)
          have e : i + 6 * (j + 1) = i + 6 + 6 * j := by ring
          rw [e]; exact this
      · intro H j hj
        have := H (j + 1) (by omega)
        have e : i + 6 * (j + 1) = i + 6 + 6 * j := by ring
        rw [e] at this; exact this

/-- Correctness of the natural-number core against `Nat.Prime`. -/
theorem isPrimeNat_eq_true_iff (n : Nat) : isPrimeNat n = true ↔ Nat.Prime n := by
  unfold isPrimeNat
  by_cases h1 : n ≤ 1
  · rw [if_pos h1]
    simp only [Bool.false_eq_true, false_iff]
    intro hp; have := hp.two_le; omega
  · rw [if_neg h1]
    by_cases h2 : n ≤ 3
    · rw [if_pos h2]
      simp only [true_iff]
      rcases (show n = 2 ∨ n = 3 by omega) with rfl | rfl
      · exact Nat.prime_two
      · exact Nat.prime_three
    · rw [if_neg h2]
      by_cases h3 : n % 2 = 0 ∨ n % 3 = 0
      · rw [if_pos h3]
        simp only [Bool.false_eq_true, false_iff]
        intro hp
        rcases h3 with h | h
        · have := hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero h); omega
        · have := hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h); omega
      · rw [if_neg h3, trialLoop_eq_true_iff]
        have hsq : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
        constructor
        · -- no candidate divides `n`, hence `n` is prime
          intro H
          by_contra hnp
          have hp : Nat.Prime n.minFac := Nat.minFac_prime (by omega)
          have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
          have hle : n.minFac ≤ Nat.sqrt n :=
            Nat.le_sqrt'.mpr (Nat.minFac_sq_le_self (by omega) hnp)
          have hmod : n % n.minFac = 0 := Nat.mod_eq_zero_of_dvd hdvd
          have hp2 : 2 ≤ n.minFac := hp.two_le
          have hn2 : n.minFac % 2 ≠ 0 := by
            intro h
            have : 2 ∣ n := dvd_trans (Nat.dvd_of_mod_eq_zero h) hdvd
            exact h3 (Or.inl (Nat.mod_eq_zero_of_dvd this))
          have hn3 : n.minFac % 3 ≠ 0 := by
            intro h
            have : 3 ∣ n := dvd_trans (Nat.dvd_of_mod_eq_zero h) hdvd
            exact h3 (Or.inr (Nat.mod_eq_zero_of_dvd this))
          generalize n.minFac = p at *
          unfold loopCount at H
          rcases (show p % 6 = 1 ∨ p % 6 = 5 by omega) with hm | hm
          · -- `p = 7 + 6 j` is the `i + 2` of the candidate `i = 5 + 6 j`
            have := H ((p - 7) / 6) (by omega)
            have e : 5 + 6 * ((p - 7) / 6) + 2 = p := by omega
            rw [e] at this
            exact this.2 hmod
          · -- `p = 5 + 6 j` is itself a candidate
            have := H ((p - 5) / 6) (by omega)
            have e : 5 + 6 * ((p - 5) / 6) = p := by omega
            rw [e] at this
            exact this.1 hmod
        · -- a prime has no divisor among the candidates
          intro hp j hj
          unfold loopCount at hj
          have hs5 : 5 ≤ Nat.sqrt n := by omega
          have h5s : 5 * Nat.sqrt n ≤ Nat.sqrt n * Nat.sqrt n := Nat.mul_le_mul_right _ hs5
          constructor
          · intro h
            have := hp.eq_one_or_self_of_dvd _ (Nat.dvd_of_mod_eq_zero h)
            omega
          · intro h
            have := hp.eq_one_or_self_of_dvd _ (Nat.dvd_of_mod_eq_zero h)
            omega

/-- The natural-number core computes `decide (Nat.Prime n)`. -/
theorem isPrimeNat_eq_decide (n : Nat) : isPrimeNat n = decide (Nat.Prime n) := by
  by_cases hp : Nat.Prime n
  · simp [hp, (isPrimeNat_eq_true_iff n).mpr hp]
  · have h : isPrimeNat n = false := by
      cases hb : isPrimeNat n
      · rfl
      · exact absurd ((isPrimeNat_eq_true_iff n).mp hb) hp
    simp [hp, h]

/-- The functional implementation on a non-negative input. -/
theorem isPrime_of_nonneg {n : Int} (h : 0 ≤ n) : isPrime n = .ok (isPrimeNat n.toNat) := by
  unfold isPrime
  rw [if_neg (not_lt.mpr h)]

/-! ### The property theorems -/

theorem isPrime_ok_thm : isPrime_ok_prop := by
  intro n hn
  exact ⟨_, isPrime_of_nonneg hn⟩

theorem isPrime_eq_prime_thm : isPrime_eq_prime_prop := by
  intro n hn
  rw [isPrime_of_nonneg hn, isPrimeNat_eq_decide]

theorem isPrime_true_iff_thm : isPrime_true_iff_prop := by
  intro n hn
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  rw [isPrime_eq_prime_thm _ hn, Int.toNat_natCast]
  simp only [Except.ok.injEq, decide_eq_true_eq]
  rw [Nat.prime_def]
  constructor
  · rintro ⟨hk, H⟩
    refine ⟨by exact_mod_cast hk, ?_⟩
    intro d hd hdk
    obtain ⟨e, rfl⟩ := Int.eq_ofNat_of_zero_le hd.le
    rcases H e (Int.natCast_dvd_natCast.mp hdk) with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  · rintro ⟨hk, H⟩
    refine ⟨by exact_mod_cast hk, ?_⟩
    intro m hm
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h
        have : k = 0 := Nat.eq_zero_of_zero_dvd hm
        omega
      · exact h
    rcases H m (by exact_mod_cast hm0) (Int.natCast_dvd_natCast.mpr hm) with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h

theorem isPrime_false_iff_thm : isPrime_false_iff_prop := by
  intro n hn
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  rw [isPrime_eq_prime_thm _ hn, Int.toNat_natCast]
  simp only [Except.ok.injEq, decide_eq_false_iff_not]
  rw [Nat.prime_def_lt']
  constructor
  · intro H
    by_cases hk : k ≤ 1
    · left; exact_mod_cast hk
    · right
      have : ¬ ∀ m : Nat, 2 ≤ m → m < k → ¬ m ∣ k := fun h => H ⟨by omega, h⟩
      push_neg at this
      obtain ⟨m, hm2, hmk, hmd⟩ := this
      exact ⟨m, by exact_mod_cast hm2, by exact_mod_cast hmk, Int.natCast_dvd_natCast.mpr hmd⟩
  · rintro (hk | ⟨d, hd1, hdk, hdd⟩) ⟨hk2, H⟩
    · have : k ≤ 1 := by exact_mod_cast hk
      omega
    · obtain ⟨e, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : Int) ≤ d)
      exact H e (by exact_mod_cast hd1) (by exact_mod_cast hdk) (Int.natCast_dvd_natCast.mp hdd)

theorem isPrime_zero_one_thm : isPrime_zero_one_prop := by
  constructor <;> rfl

theorem isPrime_neg_thm : isPrime_neg_prop := by
  intro n hn
  unfold isPrime
  rw [if_pos hn]

/-! ## Post-condition -/

/-- Post-condition relating an admissible input `n` to the result `r` of
`is_prime(n)`: no exception, the answer agrees with `Nat.Prime`, with the
docstring's definition of primality, and with the composite characterisation. -/
def Post_prop (n : Int) (r : Except String Bool) : Prop :=
  (∃ b : Bool, r = .ok b) ∧
  r = .ok (decide (Nat.Prime n.toNat)) ∧
  (r = .ok true ↔ 1 < n ∧ ∀ d : Int, 0 < d → d ∣ n → d = 1 ∨ d = n) ∧
  (r = .ok false ↔ n ≤ 1 ∨ ∃ d : Int, 1 < d ∧ d < n ∧ d ∣ n)

/-! ## Property-based tests -/

-- `isPrime_ok_prop`
#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n → ∃ b : Bool, isPrime n = .ok b)
example : (List.range 300).all (fun n => decide (∃ b : Bool, isPrime n = .ok b)) = true := by
  native_decide

-- `isPrime_eq_prime_prop`
#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n → isPrime n = .ok (decide (Nat.Prime n.toNat)))
example : (List.range 1000).all (fun n => isPrime n = .ok (decide (Nat.Prime n))) = true := by
  native_decide

-- `isPrime_true_iff_prop` (executable form: positive divisors of `n` are bounded
-- by `n`, so the quantifier ranges over `d ≤ n`)
#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n →
  decide (isPrime n = .ok true) =
    decide (1 < n ∧ ∀ d : Nat, d ≤ n.toNat → 0 < d → (d : Int) ∣ n → (d : Int) = 1 ∨ (d : Int) = n))
example : (List.range 300).all (fun n =>
    decide (isPrime n = .ok true) ==
      decide (1 < n ∧ ∀ d : Nat, d ≤ n → 0 < d → d ∣ n → d = 1 ∨ d = n)) = true := by
  native_decide

-- `isPrime_false_iff_prop` (executable form: the witness `d` is bounded by `n`)
#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n →
  decide (isPrime n = .ok false) =
    decide (n ≤ 1 ∨ ∃ d : Nat, d < n.toNat ∧ 1 < d ∧ (d : Int) ∣ n))
example : (List.range 300).all (fun n =>
    decide (isPrime n = .ok false) == decide (n ≤ 1 ∨ ∃ d : Nat, d < n ∧ 1 < d ∧ d ∣ n)) = true := by
  native_decide

-- `isPrime_zero_one_prop`
example : (isPrime 0 = .ok false ∧ isPrime 1 = .ok false) := by native_decide

-- `isPrime_neg_prop` (every negative integer is `-(k + 1)` for some `k : Nat`)
#eval Plausible.Testable.check (∀ n : Int, n < 0 → isPrime n = .error "Input must be non-negative integer")
#eval Plausible.Testable.check
  (∀ k : Nat, isPrime (-(k : Int) - 1) = .error "Input must be non-negative integer")
example : (List.range 100).all (fun n =>
    isPrime (-(n : Int) - 1) = .error "Input must be non-negative integer") = true := by
  native_decide

-- `Post_prop` (executable form of the conjunction)
#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n →
  (∃ b : Bool, isPrime n = .ok b) ∧
  isPrime n = .ok (decide (Nat.Prime n.toNat)) ∧
  decide (isPrime n = .ok true) =
    decide (1 < n ∧ ∀ d : Nat, d ≤ n.toNat → 0 < d → (d : Int) ∣ n → (d : Int) = 1 ∨ (d : Int) = n) ∧
  decide (isPrime n = .ok false) =
    decide (n ≤ 1 ∨ ∃ d : Nat, d < n.toNat ∧ 1 < d ∧ (d : Int) ∣ n))
example : (List.range 300).all (fun n =>
    decide (∃ b : Bool, isPrime n = .ok b) &&
    decide (isPrime n = .ok (decide (Nat.Prime n))) &&
    (decide (isPrime n = .ok true) ==
      decide (1 < n ∧ ∀ d : Nat, d ≤ n → 0 < d → d ∣ n → d = 1 ∨ d = n)) &&
    (decide (isPrime n = .ok false) == decide (n ≤ 1 ∨ ∃ d : Nat, d < n ∧ 1 < d ∧ d ∣ n))) = true := by
  native_decide

/-! ## Correctness theorem: `Pre → Post` -/

theorem isPrime_correct : ∀ n : Int, Pre n → Post_prop n (isPrime n) := by
  intro n hn
  exact ⟨isPrime_ok_thm n hn, isPrime_eq_prime_thm n hn, isPrime_true_iff_thm n hn,
    isPrime_false_iff_thm n hn⟩

/-! ## Imperative implementation -/

/-- Imperative translation of `is_prime`, following the Python control flow:
guards with early `return`, then a `for` loop over `range(5, isqrt(n) + 1, 6)`
with an early `return False`. -/
def isPrimeImp (n : Int) : Except String Bool := Id.run do
  if n < 0 then
    return .error "Input must be non-negative integer"
  let m : Nat := n.toNat
  if m ≤ 1 then
    return .ok false
  if m ≤ 3 then
    return .ok true
  if m % 2 == 0 || m % 3 == 0 then
    return .ok false
  -- Check all numbers of form 6k ± 1 up to sqrt(n)
  for i in [5:Nat.sqrt m + 1:6] do
    if m % i == 0 || m % (i + 2) == 0 then
      return .ok false
  return .ok true

/-! ## Imperative tests -/

example : isPrimeImp 2 = .ok true := by native_decide
example : isPrimeImp 4 = .ok false := by native_decide
example : isPrimeImp 0 = .ok false := by native_decide
example : isPrimeImp 7 = .ok true := by native_decide
example : isPrimeImp 25 = .ok false := by native_decide
example : isPrimeImp 49 = .ok false := by native_decide
example : isPrimeImp 7919 = .ok true := by native_decide
example : isPrimeImp (-1) = .error "Input must be non-negative integer" := by native_decide

#eval isPrimeImp 7      -- Except.ok true
#eval isPrimeImp 0      -- Except.ok false
#eval isPrimeImp (-1)   -- Except.error "Input must be non-negative integer"

-- PBT: functional and imperative implementations agree
#eval Plausible.Testable.check (∀ n : Int, isPrime n = isPrimeImp n)
example : (List.range 500).all (fun n => isPrime n = isPrimeImp n) = true := by native_decide

/-! ## Equivalence theorem -/

/-- The loop body of `isPrimeImp`, exactly as produced by the `do`-notation
(the loop state is `MProd (Option result) PUnit`: `some r` signals an early
`return r`). -/
def loopBody (m : Nat) (i : Nat) (_r : MProd (Option (Except String Bool)) PUnit) :
    Id (ForInStep (MProd (Option (Except String Bool)) PUnit)) :=
  if (m % i == 0 || m % (i + 2) == 0) = true then
    pure (ForInStep.done ⟨some (Except.ok false), PUnit.unit⟩)
  else pure (ForInStep.yield ⟨none, PUnit.unit⟩)

/-- Running the imperative loop over `List.range' i count 6` computes the
functional `trialLoop`. -/
theorem forIn_loopBody (m i count : Nat) :
    (forIn (m := Id) (List.range' i count 6)
        (⟨none, PUnit.unit⟩ : MProd (Option (Except String Bool)) PUnit) (loopBody m))
      = ⟨if trialLoop m i count then none else some (Except.ok false), PUnit.unit⟩ := by
  induction count generalizing i with
  | zero => simp [trialLoop]; rfl
  | succ k ih =>
    rw [List.range'_succ, List.forIn_cons]
    simp only [trialLoop, loopBody]
    by_cases h : m % i = 0 ∨ m % (i + 2) = 0
    · have hb : (m % i == 0 || m % (i + 2) == 0) = true := by
        simpa [Bool.or_eq_true, beq_iff_eq] using h
      simp [hb, h]; rfl
    · have hb : ¬ ((m % i == 0 || m % (i + 2) == 0) = true) := by
        simpa [Bool.or_eq_true, beq_iff_eq] using h
      simp [hb, h, ih]

/-- Functional and imperative implementations agree on every input. -/
theorem isPrime_eq_isPrimeImp : ∀ n : Int, isPrime n = isPrimeImp n := by
  intro n
  unfold isPrime isPrimeImp
  by_cases hn : n < 0
  · simp [hn]
  · simp only [hn, if_false]
    generalize n.toNat = m
    have hbody : (fun (i : Nat) (r : MProd (Option (Except String Bool)) PUnit) =>
        if (m % i == 0 || m % (i + 2) == 0) = true then
          (pure (ForInStep.done ⟨some (Except.ok false), PUnit.unit⟩) : Id _)
        else do
          pure PUnit.unit
          pure (ForInStep.yield ⟨none, PUnit.unit⟩)) = loopBody m := by
      funext i r; rfl
    rw [hbody, Std.Range.forIn_eq_forIn_range']
    have hsize : (Std.Range.size { start := 5, stop := m.sqrt + 1, step := 6, step_pos := by norm_num })
        = loopCount m := by
      simp only [Std.Range.size, loopCount]; omega
    rw [hsize, forIn_loopBody]
    unfold isPrimeNat
    by_cases h1 : m ≤ 1
    · simp [h1]
    · by_cases h2 : m ≤ 3
      · simp [h1, h2]
      · by_cases h3 : m % 2 = 0 ∨ m % 3 = 0
        · have hb : (m % 2 == 0 || m % 3 == 0) = true := by simpa using h3
          simp [h1, h2, h3, hb]
        · have hb : ¬ (m % 2 == 0 || m % 3 == 0) = true := by simpa using h3
          simp only [h1, h2, h3, hb, if_false]
          cases trialLoop m 5 (loopCount m) <;> rfl

end «23_is_prime»
