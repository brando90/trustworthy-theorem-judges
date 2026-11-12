import Mathlib

/-!
# HumanEval/39 -- `prime_fib`

`prime_fib n` returns the `n`-th number that is both a Fibonacci number and a prime
(`prime_fib 1 = 2`, `prime_fib 2 = 3`, `prime_fib 3 = 5`, `prime_fib 4 = 13`, ...).

The Python program keeps the Fibonacci sequence `f = [0, 1]`, repeatedly appends
`f[-1] + f[-2]`, tests the new element with a trial-division primality test `is_prime`,
decrements `n` whenever the new element is prime and returns the new element as soon as
`n == 0`.

It is an open problem whether there are infinitely many Fibonacci primes, so the Python
`while True` loop cannot be proved terminating in general.  We therefore model the loop
with an explicit `fuel` (maximal number of loop iterations, default `1000`) and return
`Option Nat`: `some r` is the value returned by Python, `none` models the case where the
allowed number of iterations is exhausted.  For the Python inputs of interest (`n ≤ 10`)
`42` iterations suffice.  (As in Python, `n = 0` returns the first generated element `1`.)

We prove that the primality test agrees with `Nat.Prime`, that every result is a prime
Fibonacci number with exactly `n - 1` prime Fibonacci numbers before it (so it is
`Nat.nth IsPrimeFib (n - 1)`, the `n`-th prime Fibonacci number), that the fuel model is
exact (`none` iff fewer than `n` of the generated Fibonacci numbers are prime), that the
result does not depend on the fuel, and that an imperative line-by-line transcription of
the Python program (with a mutable array `f`) agrees with the functional implementation.
-/

namespace humaneval_39_prime_fib

/-! ## Functional implementation -/

/-- Python's `is_prime`: `p ≥ 2` and `p % k ≠ 0` for every
`k ∈ range(2, min(int(math.sqrt(p)) + 1, p - 1))` (`int(math.sqrt p)` is `Nat.sqrt p`). -/
def isPrime (p : Nat) : Bool :=
  if p < 2 then false
  else
    let hi := min (Nat.sqrt p + 1) (p - 1)
    (List.range' 2 (hi - 2)).all fun k => p % k != 0

/-- The Python `while True` loop.  The state is `a = f[-2]`, `b = f[-1]` and `n`, the number
of prime Fibonacci numbers still to be found; `fuel` bounds the number of iterations.
Each iteration appends `c = a + b` to the sequence, decrements `n` if `c` is prime and
returns `c` as soon as `n` is `0`. -/
def primeFibLoop : Nat → Nat → Nat → Nat → Option Nat
  | 0, _, _, _ => none
  | fuel + 1, a, b, n =>
    let c := a + b
    let n' := if isPrime c then n - 1 else n
    if n' = 0 then some c else primeFibLoop fuel b c n'

/-- `prime_fib n`: the `n`-th number that is a Fibonacci number and also prime.
The sequence starts from `f = [0, 1]`; `none` means that `fuel` loop iterations did not
suffice. -/
def primeFib (n : Nat) (fuel : Nat := 1000) : Option Nat :=
  primeFibLoop fuel 0 1 n

/-! ## Unit tests -/

example : primeFib 1 = some 2 := by native_decide
example : primeFib 2 = some 3 := by native_decide
example : primeFib 3 = some 5 := by native_decide
example : primeFib 4 = some 13 := by native_decide
example : primeFib 5 = some 89 := by native_decide
example : primeFib 6 = some 233 := by native_decide
example : primeFib 7 = some 1597 := by native_decide
example : primeFib 8 = some 28657 := by native_decide
example : primeFib 9 = some 514229 := by native_decide
example : primeFib 10 = some 433494437 := by native_decide
-- as in Python, `prime_fib(0)` returns the first generated element `1` (which is not prime)
example : primeFib 0 = some 1 := by native_decide
-- not enough fuel
example : primeFib 5 3 = none := by native_decide
example : primeFib 10 42 = some 433494437 := by native_decide
example : primeFib 10 41 = none := by native_decide
example : isPrime 0 = false := by native_decide
example : isPrime 1 = false := by native_decide
example : isPrime 2 = true := by native_decide
example : isPrime 3 = true := by native_decide
example : isPrime 4 = false := by native_decide
example : isPrime 9 = false := by native_decide
example : isPrime 89 = true := by native_decide

#eval primeFib 1
#eval primeFib 5
#eval primeFib 10
#eval (List.range 10).map fun i => primeFib (i + 1)

/-! ## Pre-condition -/

/-- Pre-condition: `n ≥ 1` (for `n = 0` the Python program returns the non-prime `1`). -/
def Pre (n : Nat) : Prop := 1 ≤ n

/-! ## Specification helpers -/

/-- `p` is a prime Fibonacci number. -/
def IsPrimeFib (p : Nat) : Prop := Nat.Prime p ∧ ∃ k, Nat.fib k = p

/-- Number of indices `j < k` whose Fibonacci number `Nat.fib j` is prime. -/
def fibPrimeCount (k : Nat) : Nat := Nat.count (fun j => Nat.Prime (Nat.fib j)) k

theorem fibPrimeCount_succ (k : Nat) :
    fibPrimeCount (k + 1) = fibPrimeCount k + if Nat.Prime (Nat.fib k) then 1 else 0 :=
  Nat.count_succ _ _

theorem fibPrimeCount_two : fibPrimeCount 2 = 0 := by
  simp [fibPrimeCount, Nat.count_succ, Nat.not_prime_zero, Nat.not_prime_one]

/-! ## Properties and theorems -/

/-- The trial-division test of the Python program agrees with `Nat.Prime`. -/
def isPrime_correct_prop : Prop := ∀ p : Nat, isPrime p = true ↔ Nat.Prime p

theorem isPrime_correct_thm : isPrime_correct_prop := by
  intro p
  unfold isPrime
  by_cases h2 : p < 2
  · simp only [h2, if_true, Bool.false_eq_true, false_iff]
    intro hp
    exact absurd hp.two_le (by omega)
  · simp only [h2, if_false, List.all_eq_true, List.mem_range'_1, bne_iff_ne, ne_eq]
    rw [Nat.prime_def_le_sqrt]
    have hsmall : p < 4 → Nat.sqrt p < 2 := fun h => Nat.sqrt_lt'.2 (by omega)
    have hbig : 4 ≤ p → Nat.sqrt p + 2 ≤ p := by
      intro h4
      have h1 : 2 ≤ Nat.sqrt p := Nat.le_sqrt.2 (by omega)
      have h2 := Nat.sqrt_le p
      nlinarith
    constructor
    · intro H
      refine ⟨by omega, fun m hm2 hms hdvd => ?_⟩
      by_cases h4 : 4 ≤ p
      · have := hbig h4
        exact H m ⟨hm2, by omega⟩ (Nat.mod_eq_zero_of_dvd hdvd)
      · have := hsmall (by omega)
        omega
    · rintro ⟨-, H⟩ k ⟨hk2, hk⟩ hmod
      exact H k hk2 (by omega) (Nat.dvd_of_mod_eq_zero hmod)

/-- The loop invariant: when the loop is entered with `a = fib i`, `b = fib (i+1)` and
`n > 0` remaining, where `n + (number of primes among fib 0, …, fib (i+1)) = N`, any
result is `fib k` for a `k` with `fib k` prime and exactly `N - 1` primes among
`fib 0, …, fib (k-1)`. -/
theorem primeFibLoop_spec (N : Nat) :
    ∀ (fuel i n r : Nat),
      n + fibPrimeCount (i + 2) = N → 0 < n →
      primeFibLoop fuel (Nat.fib i) (Nat.fib (i + 1)) n = some r →
      ∃ k, Nat.fib k = r ∧ Nat.Prime r ∧ fibPrimeCount k = N - 1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro i n r _ _ h
    simp [primeFibLoop] at h
  | succ fuel ih =>
    intro i n r hN hn h
    have hc : Nat.fib i + Nat.fib (i + 1) = Nat.fib (i + 2) := Nat.fib_add_two.symm
    simp only [primeFibLoop, hc] at h
    have hcnt : fibPrimeCount (i + 1 + 2) =
        fibPrimeCount (i + 2) + if Nat.Prime (Nat.fib (i + 2)) then 1 else 0 :=
      fibPrimeCount_succ (i + 2)
    by_cases hp : Nat.Prime (Nat.fib (i + 2))
    · have hb : isPrime (Nat.fib (i + 2)) = true := (isPrime_correct_thm _).2 hp
      rw [if_pos hb] at h
      rw [if_pos hp] at hcnt
      by_cases hz : n - 1 = 0
      · rw [if_pos hz] at h
        obtain rfl := Option.some.inj h
        exact ⟨i + 2, rfl, hp, by omega⟩
      · rw [if_neg hz] at h
        exact ih (i + 1) (n - 1) r (by omega) (by omega) h
    · have hb : ¬ isPrime (Nat.fib (i + 2)) = true :=
        fun h' => hp ((isPrime_correct_thm _).1 h')
      rw [if_neg hb] at h
      rw [if_neg hp] at hcnt
      have hz : ¬ n = 0 := by omega
      rw [if_neg hz] at h
      exact ih (i + 1) n r (by omega) hn h

/-- Main specification of the functional implementation. -/
theorem primeFib_spec (n fuel r : Nat) (hn : 1 ≤ n) (h : primeFib n fuel = some r) :
    ∃ k, Nat.fib k = r ∧ Nat.Prime r ∧ fibPrimeCount k = n - 1 := by
  have key := primeFibLoop_spec n fuel 0 n r (by simp [fibPrimeCount_two]) hn
  simp only [Nat.fib_zero, zero_add, Nat.fib_one] at key
  exact key h

/-- A prime Fibonacci number has index at least `3` (`fib 0 = 0`, `fib 1 = fib 2 = 1`). -/
theorem three_le_of_prime_fib {j : Nat} (h : Nat.Prime (Nat.fib j)) : 3 ≤ j := by
  match j with
  | 0 => simp [Nat.not_prime_zero] at h
  | 1 => simp [Nat.not_prime_one] at h
  | 2 => simp [Nat.fib_two, Nat.not_prime_one] at h
  | j + 3 => omega

/-- Counting prime Fibonacci numbers below `fib k` (by value) is the same as counting the
indices `j < k` with `fib j` prime. -/
theorem count_isPrimeFib_fib [DecidablePred IsPrimeFib] (k : Nat) (hk : Nat.Prime (Nat.fib k)) :
    Nat.count IsPrimeFib (Nat.fib k) = fibPrimeCount k := by
  unfold fibPrimeCount
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  have hk3 := three_le_of_prime_fib hk
  have himg : (Finset.range (Nat.fib k)).filter IsPrimeFib
      = ((Finset.range k).filter fun j => Nat.Prime (Nat.fib j)).image Nat.fib := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, IsPrimeFib]
    constructor
    · rintro ⟨hx, hpx, j, rfl⟩
      refine ⟨j, ⟨?_, hpx⟩, rfl⟩
      by_contra hjk
      exact absurd (Nat.fib_mono (not_lt.1 hjk)) (not_le.2 hx)
    · rintro ⟨j, ⟨hjk, hpj⟩, rfl⟩
      have hj3 := three_le_of_prime_fib hpj
      exact ⟨(Nat.fib_lt_fib (by omega)).2 hjk, hpj, j, rfl⟩
  rw [himg, Finset.card_image_of_injOn]
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
  have ha3 := three_le_of_prime_fib ha.2
  have hb3 := three_le_of_prime_fib hb.2
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := (Nat.fib_lt_fib (by omega)).2 hlt
    omega
  · have := (Nat.fib_lt_fib (by omega)).2 hlt
    omega

/-- If `fib k` is prime and exactly `m` earlier Fibonacci numbers are prime, then `fib k`
is the `m`-th (0-indexed) prime Fibonacci number. -/
theorem nth_isPrimeFib_eq (k m : Nat) (hk : Nat.Prime (Nat.fib k)) (hc : fibPrimeCount k = m) :
    Nat.nth IsPrimeFib m = Nat.fib k := by
  classical
  have h := Nat.nth_count (p := IsPrimeFib) (n := Nat.fib k) ⟨hk, k, rfl⟩
  rwa [count_isPrimeFib_fib k hk, hc] at h

set_option linter.unusedVariables false in
/-- Property: every returned value is prime. -/
def result_prime_prop (n : Nat) (res : Option Nat) : Prop :=
  ∀ r, res = some r → Nat.Prime r

theorem result_prime_thm (n fuel : Nat) (h : Pre n) : result_prime_prop n (primeFib n fuel) := by
  intro r hr
  obtain ⟨k, -, hp, -⟩ := primeFib_spec n fuel r h hr
  exact hp

set_option linter.unusedVariables false in
/-- Property: every returned value is a Fibonacci number. -/
def result_fib_prop (n : Nat) (res : Option Nat) : Prop :=
  ∀ r, res = some r → ∃ k, Nat.fib k = r

theorem result_fib_thm (n fuel : Nat) (h : Pre n) : result_fib_prop n (primeFib n fuel) := by
  intro r hr
  obtain ⟨k, hk, -, -⟩ := primeFib_spec n fuel r h hr
  exact ⟨k, hk⟩

/-- Property: the returned value is `fib k` where exactly `n - 1` of the earlier Fibonacci
numbers `fib 0, …, fib (k - 1)` are prime, i.e. it is the `n`-th prime met by the loop. -/
def result_count_prop (n : Nat) (res : Option Nat) : Prop :=
  ∀ r, res = some r → ∃ k, Nat.fib k = r ∧ fibPrimeCount k = n - 1

theorem result_count_thm (n fuel : Nat) (h : Pre n) : result_count_prop n (primeFib n fuel) := by
  intro r hr
  obtain ⟨k, hk, -, hc⟩ := primeFib_spec n fuel r h hr
  exact ⟨k, hk, hc⟩

/-- Property: the returned value is the `n`-th (1-indexed) prime Fibonacci number. -/
def result_nth_prop (n : Nat) (res : Option Nat) : Prop :=
  ∀ r, res = some r → Nat.nth IsPrimeFib (n - 1) = r

theorem result_nth_thm (n fuel : Nat) (h : Pre n) : result_nth_prop n (primeFib n fuel) := by
  intro r hr
  obtain ⟨k, hk, hp, hc⟩ := primeFib_spec n fuel r h hr
  rw [← hk] at hp ⊢
  exact nth_isPrimeFib_eq k (n - 1) hp hc

/-- Property: the result does not depend on the amount of fuel (whenever it exists). -/
def result_unique_prop (n : Nat) : Prop :=
  ∀ f₁ f₂ r₁ r₂, primeFib n f₁ = some r₁ → primeFib n f₂ = some r₂ → r₁ = r₂

theorem result_unique_thm (n : Nat) (h : Pre n) : result_unique_prop n := by
  intro f₁ f₂ r₁ r₂ h₁ h₂
  have e₁ := result_nth_thm n f₁ h r₁ h₁
  have e₂ := result_nth_thm n f₂ h r₂ h₂
  rw [← e₁, ← e₂]

/-- Property (Python edge case): `prime_fib 0` returns the first generated element `1`. -/
def zero_case_prop : Prop := ∀ fuel, 1 ≤ fuel → primeFib 0 fuel = some 1

theorem zero_case_thm : zero_case_prop := by
  intro fuel hfuel
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  simp [primeFib, primeFibLoop, isPrime]

theorem fibPrimeCount_mono {a b : Nat} (h : a ≤ b) : fibPrimeCount a ≤ fibPrimeCount b :=
  Nat.count_monotone _ h

/-- Exact characterization of fuel exhaustion for the loop: entered with `a = fib i`,
`b = fib (i+1)` and `n > 0` remaining, the loop runs out of `fuel` iff fewer than `n` of
the next `fuel` Fibonacci numbers `fib (i+2), …, fib (i+1+fuel)` are prime. -/
theorem primeFibLoop_eq_none_iff :
    ∀ (fuel i n : Nat), 0 < n →
      (primeFibLoop fuel (Nat.fib i) (Nat.fib (i + 1)) n = none ↔
        fibPrimeCount (i + 2 + fuel) < n + fibPrimeCount (i + 2)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i n hn
    simp only [primeFibLoop, Nat.add_zero, true_iff]
    omega
  | succ fuel ih =>
    intro i n hn
    have hc : Nat.fib i + Nat.fib (i + 1) = Nat.fib (i + 2) := Nat.fib_add_two.symm
    simp only [primeFibLoop, hc]
    have hcnt : fibPrimeCount (i + 1 + 2) =
        fibPrimeCount (i + 2) + if Nat.Prime (Nat.fib (i + 2)) then 1 else 0 :=
      fibPrimeCount_succ (i + 2)
    have hidx : i + 1 + 2 + fuel = i + 2 + (fuel + 1) := by omega
    have hmono : fibPrimeCount (i + 1 + 2) ≤ fibPrimeCount (i + 2 + (fuel + 1)) :=
      fibPrimeCount_mono (by omega)
    by_cases hp : Nat.Prime (Nat.fib (i + 2))
    · have hb : isPrime (Nat.fib (i + 2)) = true := (isPrime_correct_thm _).2 hp
      rw [if_pos hb]
      rw [if_pos hp] at hcnt
      by_cases hz : n - 1 = 0
      · rw [if_pos hz]
        simp only [Option.some_ne_none, false_iff, not_lt]
        omega
      · have ih' := ih (i + 1) (n - 1) (by omega)
        rw [show i + 1 + 1 = i + 2 from rfl, hidx] at ih'
        rw [if_neg hz, ih']
        constructor <;> intro h <;> omega
    · have hb : ¬ isPrime (Nat.fib (i + 2)) = true :=
        fun h' => hp ((isPrime_correct_thm _).1 h')
      rw [if_neg hb]
      rw [if_neg hp] at hcnt
      have hz : ¬ n = 0 := by omega
      have ih' := ih (i + 1) n hn
      rw [show i + 1 + 1 = i + 2 from rfl, hidx] at ih'
      rw [if_neg hz, ih']
      constructor <;> intro h <;> omega

/-- Property: the fuel model is exact -- `prime_fib n` fails to return within `fuel` loop
iterations iff fewer than `n` of the generated Fibonacci numbers `fib 2, …, fib (fuel + 1)`
are prime. -/
def none_iff_prop (n : Nat) : Prop :=
  ∀ fuel, primeFib n fuel = none ↔ fibPrimeCount (fuel + 2) < n

theorem none_iff_thm (n : Nat) (h : Pre n) : none_iff_prop n := by
  intro fuel
  have key := primeFibLoop_eq_none_iff fuel 0 n h
  simp only [Nat.fib_zero, zero_add, Nat.fib_one, fibPrimeCount_two, add_zero] at key
  rw [Nat.add_comm 2 fuel] at key
  exact key

/-- Property: more fuel never changes an answer that was already found. -/
def fuel_mono_prop (n : Nat) : Prop :=
  ∀ fuel fuel' r, fuel ≤ fuel' → primeFib n fuel = some r → primeFib n fuel' = some r

theorem fuel_mono_thm (n : Nat) (h : Pre n) : fuel_mono_prop n := by
  intro fuel fuel' r hle hsome
  have h1 : ¬ primeFib n fuel = none := by rw [hsome]; simp
  rw [none_iff_thm n h fuel, not_lt] at h1
  have h2 : ¬ primeFib n fuel' = none := by
    rw [none_iff_thm n h fuel', not_lt]
    exact le_trans h1 (fibPrimeCount_mono (by omega))
  obtain ⟨r', hr'⟩ := Option.ne_none_iff_exists'.1 h2
  rw [hr', result_unique_thm n h fuel fuel' r r' hsome hr']

/-! ## Post-condition -/

/-- Post-condition: conjunction of the result properties. -/
def Post_prop (n : Nat) (res : Option Nat) : Prop :=
  result_prime_prop n res ∧ result_fib_prop n res ∧ result_count_prop n res ∧
    result_nth_prop n res

/-! ## Property-based tests -/

-- isPrime_correct_prop
#eval Plausible.Testable.check (∀ p : Nat, isPrime p = decide (Nat.Prime p))
example : (List.range 2000).all (fun p => isPrime p == decide (Nat.Prime p)) = true := by
  native_decide

/-- Executable helper: is `r` a Fibonacci number (with index below 60)? -/
def isFibBelow60 (r : Nat) : Bool := (List.range 60).any fun k => Nat.fib k == r

/-- Executable helper: the prime Fibonacci numbers among `fib 0, …, fib 49`, in order. -/
def primeFibsBelow50 : List Nat :=
  ((List.range 50).map Nat.fib).filter fun x => decide (Nat.Prime x)

#eval primeFibsBelow50

-- the program returns a value for all tested inputs
example : (List.range 10).all (fun i => (primeFib (i + 1)).isSome) = true := by native_decide
-- result_prime_prop
example : (List.range 10).all (fun i => (primeFib (i + 1)).all fun r => decide (Nat.Prime r)) =
    true := by native_decide
-- result_fib_prop
example : (List.range 10).all (fun i => (primeFib (i + 1)).all isFibBelow60) = true := by
  native_decide
-- result_count_prop
example : (List.range 10).all (fun i => (primeFib (i + 1)).all fun r =>
    (List.range 60).any fun k => Nat.fib k == r && fibPrimeCount k == i) = true := by
  native_decide
-- result_nth_prop (`Nat.nth` is noncomputable; we test against the enumerated list of
-- prime Fibonacci numbers, which is its executable counterpart)
example : (List.range 10).all (fun i => primeFib (i + 1) == primeFibsBelow50[i]?) = true := by
  native_decide
-- result_unique_prop
example : (List.range 10).all (fun i =>
    primeFib (i + 1) 42 == primeFib (i + 1) 100 && primeFib (i + 1) 100 == primeFib (i + 1)) =
    true := by native_decide
-- zero_case_prop
example : (List.range 50).all (fun f => primeFib 0 (f + 1) == some 1) = true := by native_decide
#eval Plausible.Testable.check (∀ f : Nat, primeFib 0 (f + 1) = some 1)
-- none_iff_prop
example : (List.range 11).all (fun n => (List.range 50).all fun fuel =>
    (primeFib (n + 1) fuel == none) == decide (fibPrimeCount (fuel + 2) < n + 1)) = true := by
  native_decide
-- fuel_mono_prop
example : (List.range 11).all (fun n => (List.range 48).all fun fuel =>
    primeFib (n + 1) fuel == none ||
      (primeFib (n + 1) (fuel + 1) == primeFib (n + 1) fuel &&
        primeFib (n + 1) 48 == primeFib (n + 1) fuel)) = true := by
  native_decide
-- Post_prop (all executable conjuncts together)
example : (List.range 10).all (fun i => (primeFib (i + 1)).all fun r =>
    decide (Nat.Prime r) && isFibBelow60 r &&
    ((List.range 60).any fun k => Nat.fib k == r && fibPrimeCount k == i) &&
    (primeFibsBelow50[i]? == some r)) = true := by
  native_decide

/-! ## Correctness theorem -/

theorem primeFib_correct (n fuel : Nat) (h : Pre n) : Post_prop n (primeFib n fuel) :=
  ⟨result_prime_thm n fuel h, result_fib_thm n fuel h, result_count_thm n fuel h,
    result_nth_thm n fuel h⟩

/-- The fuel model is faithful: `none` exactly when the fuel is insufficient, more fuel never
changes an answer, and the answer is unique. -/
theorem primeFib_fuel_model (n : Nat) (h : Pre n) :
    none_iff_prop n ∧ fuel_mono_prop n ∧ result_unique_prop n :=
  ⟨none_iff_thm n h, fuel_mono_thm n h, result_unique_thm n h⟩

/-! ## Imperative implementation -/

/-- The imperative loop with explicit initial state: `f` is the Python list `f` (the
Fibonacci numbers generated so far, initially `[0, 1]`) and `n` the remaining count; the
list `l` only bounds the number of iterations, like `fuel` in `primeFibLoop`. -/
def primeFibImpAux (l : List Nat) (f : Array Nat) (n : Nat) : Option Nat := Id.run do
  let mut f := f
  let mut rem := n
  for _ in l do
    f := f.push (f[f.size - 1]! + f[f.size - 2]!)   -- f.append(f[-1] + f[-2])
    if isPrime f[f.size - 1]! then                  -- if is_prime(f[-1]):
      rem := rem - 1                                --     n -= 1
    if rem = 0 then                                 -- if n == 0:
      return some f[f.size - 1]!                    --     return f[-1]
  return none

/-- Imperative `prime_fib`, a line-by-line transcription of the Python program with mutable
state (the `while True` loop is bounded by `fuel` iterations). -/
def primeFibImp (n : Nat) (fuel : Nat := 1000) : Option Nat := Id.run do
  let mut f : Array Nat := #[0, 1]                  -- f = [0, 1]
  let mut rem := n
  for _ in List.range fuel do                       -- while True: (bounded by fuel)
    f := f.push (f[f.size - 1]! + f[f.size - 2]!)   --   f.append(f[-1] + f[-2])
    if isPrime f[f.size - 1]! then                  --   if is_prime(f[-1]):
      rem := rem - 1                                --       n -= 1
    if rem = 0 then                                 --   if n == 0:
      return some f[f.size - 1]!                    --       return f[-1]
  return none

/-! ## Imperative tests -/

example : primeFibImp 1 = some 2 := by native_decide
example : primeFibImp 2 = some 3 := by native_decide
example : primeFibImp 3 = some 5 := by native_decide
example : primeFibImp 4 = some 13 := by native_decide
example : primeFibImp 5 = some 89 := by native_decide
example : primeFibImp 6 = some 233 := by native_decide
example : primeFibImp 7 = some 1597 := by native_decide
example : primeFibImp 8 = some 28657 := by native_decide
example : primeFibImp 9 = some 514229 := by native_decide
example : primeFibImp 10 = some 433494437 := by native_decide
example : primeFibImp 0 = some 1 := by native_decide
example : primeFibImp 5 3 = none := by native_decide

#eval primeFibImp 10
#eval (List.range 10).map fun i => primeFibImp (i + 1)

-- PBT for the equivalence
example : (List.range 12).all (fun i => primeFibImp i == primeFib i) = true := by native_decide
example : (List.range 12).all (fun i => (List.range 50).all fun f =>
    primeFibImp i f == primeFib i f) = true := by native_decide

/-! ## Equivalence theorem -/

theorem push_last (f : Array Nat) (c : Nat) : (f.push c)[(f.push c).size - 1]! = c := by
  rw [Array.size_push, Nat.add_sub_cancel]
  simp

theorem push_prev (f : Array Nat) (c : Nat) (hf : 1 ≤ f.size) :
    (f.push c)[(f.push c).size - 2]! = f[f.size - 1]! := by
  rw [Array.size_push, show f.size + 1 - 2 = f.size - 1 by omega]
  have hlt : f.size - 1 < f.size := by omega
  rw [getElem!_pos (f.push c) (f.size - 1) (by rw [Array.size_push]; omega),
    getElem!_pos f (f.size - 1) hlt]
  exact Array.getElem_push_lt hlt

/-- The imperative loop started on an array `f` (with at least two elements) behaves like
the functional loop started on the last two elements of `f`. -/
theorem primeFibImpAux_eq (l : List Nat) :
    ∀ (f : Array Nat) (n : Nat), 2 ≤ f.size →
      primeFibImpAux l f n = primeFibLoop l.length f[f.size - 2]! f[f.size - 1]! n := by
  induction l with
  | nil => intro f n _; rfl
  | cons x l ih =>
    intro f n hf
    simp only [List.length_cons, primeFibLoop]
    rw [Nat.add_comm f[f.size - 2]! f[f.size - 1]!]
    have hlast := push_last f (f[f.size - 1]! + f[f.size - 2]!)
    have hprev := push_prev f (f[f.size - 1]! + f[f.size - 2]!) (by omega)
    have ih' := fun n' => ih (f.push (f[f.size - 1]! + f[f.size - 2]!)) n'
      (by rw [Array.size_push]; omega)
    simp only [hlast, hprev] at ih'
    by_cases hp : isPrime (f[f.size - 1]! + f[f.size - 2]!) = true
    · by_cases hz : n - 1 = 0
      · simp [primeFibImpAux, List.forIn_cons, hp, hz]
      · rw [if_pos hp, if_neg hz, ← ih' (n - 1)]
        simp [primeFibImpAux, List.forIn_cons, hp, hz]
    · by_cases hz : n = 0
      · simp [primeFibImpAux, List.forIn_cons, hp, hz]
      · rw [if_neg hp, if_neg hz, ← ih' n]
        simp [primeFibImpAux, List.forIn_cons, hp, hz]

theorem primeFibImp_eq_aux (n fuel : Nat) :
    primeFibImp n fuel = primeFibImpAux (List.range fuel) #[0, 1] n := rfl

/-- The imperative implementation agrees with the functional one. -/
theorem primeFibImp_eq_primeFib (n fuel : Nat) : primeFibImp n fuel = primeFib n fuel := by
  rw [primeFibImp_eq_aux, primeFibImpAux_eq (List.range fuel) #[0, 1] n (by simp),
    List.length_range]
  rfl

end humaneval_39_prime_fib
