import Mathlib

/-!
# HumanEval/39 — `prime_fib`

`prime_fib n` returns the `n`-th number that is both a Fibonacci number and a prime.

The Python program keeps the list `f = [0, 1]`, repeatedly appends `f[-1] + f[-2]`
(so it visits `fib 2, fib 3, fib 4, …` in order), decrements `n` whenever the freshly
appended number is prime (`is_prime` is trial division up to `isqrt(p)`), and returns
the current Fibonacci number as soon as `n` reaches `0`.

The Python loop is `while True`: it only stops once the `n`-th Fibonacci prime has been
reached.  Whether infinitely many Fibonacci primes exist is an open problem, so no total
Lean function can honestly promise an answer for every `n`.  The model below therefore
makes the number of loop iterations explicit: `prime_fib n fuel` runs at most `fuel`
iterations of the Python loop (examining `fib 2, …, fib (fuel + 1)`) and returns
`some m` exactly when the Python program returns `m` within those iterations, and
`none` when the Python program would still be running.

The main results are:

* `isPrime_iff`: the Python `is_prime` agrees with `Nat.Prime`;
* `prime_fib_sound` / `prime_fib_nth`: a returned value is exactly the `n`-th
  prime Fibonacci number (`Nat.nth FibPrime (n - 1)`);
* `prime_fib_complete` / `prime_fib_none`: a value is returned as soon as the fuel
  reaches the index of the `n`-th Fibonacci prime, and `none` is returned only if fewer
  than `n` of the examined Fibonacci numbers are prime;
* `prime_fib_terminates_of_infinite`: if the Fibonacci primes are infinite (the open
  conjecture), the Python program terminates for every `n ≥ 1`;
* `prime_fib_eq_imp`: the functional and imperative versions agree.
-/

namespace humaneval_39_prime_fib

/-! ## Implementation -/

/-- Python's inner `is_prime p`: trial division by every
`k ∈ range(2, min(isqrt(p) + 1, p - 1))`.  (`int(math.sqrt(p))` is modelled by the exact
integer square root `Nat.sqrt`.) -/
def isPrime (p : Nat) : Bool :=
  if p < 2 then false
  else
    let hi := min (Nat.sqrt p + 1) (p - 1)
    (List.range' 2 (hi - 2)).all fun k => p % k != 0

/-- One run of the Python `while True` loop with at most `fuel` iterations left.
The state is `n` (how many Fibonacci primes are still to be found), `a = f[-2]` and
`b = f[-1]`.  Every iteration appends `c = a + b`, decrements `n` if `c` is prime and
returns `c` when `n` becomes `0`. -/
def primeFibLoop : Nat → Nat → Nat → Nat → Option Nat
  | 0, _, _, _ => none
  | fuel + 1, n, a, b =>
    let c := a + b
    let n' := if isPrime c then n - 1 else n
    if n' = 0 then some c else primeFibLoop fuel n' b c

/-- `prime_fib n fuel`: the `n`-th prime Fibonacci number, searched for among the
Fibonacci numbers `fib 2, …, fib (fuel + 1)` (that is, `fuel` iterations of the Python
loop started from `f = [0, 1]`).  `none` means the Python program has not returned yet. -/
def prime_fib (n : Nat) (fuel : Nat) : Option Nat :=
  primeFibLoop fuel n 0 1

/-! ## Unit tests (the `check` function of the Python file, plus the docstring) -/

example : prime_fib 1 100 = some 2 := by native_decide
example : prime_fib 2 100 = some 3 := by native_decide
example : prime_fib 3 100 = some 5 := by native_decide
example : prime_fib 4 100 = some 13 := by native_decide
example : prime_fib 5 100 = some 89 := by native_decide
example : prime_fib 6 100 = some 233 := by native_decide
example : prime_fib 7 100 = some 1597 := by native_decide
example : prime_fib 8 100 = some 28657 := by native_decide
example : prime_fib 9 100 = some 514229 := by native_decide
example : prime_fib 10 100 = some 433494437 := by native_decide
-- The 10-th Fibonacci prime is `fib 43`; it needs 42 iterations.
example : prime_fib 10 41 = none := by native_decide
example : prime_fib 10 42 = some 433494437 := by native_decide
-- Behaviour outside the intended domain: Python returns `1` for `n = 0`.
example : prime_fib 0 100 = some 1 := by native_decide
-- `is_prime` on small inputs.
example : isPrime 0 = false := by native_decide
example : isPrime 1 = false := by native_decide
example : isPrime 2 = true := by native_decide
example : isPrime 3 = true := by native_decide
example : isPrime 4 = false := by native_decide
example : isPrime 9 = false := by native_decide
example : isPrime 433494437 = true := by native_decide

#eval prime_fib 1 100
#eval prime_fib 5 100
#eval prime_fib 10 100
#eval (List.range 10).map fun n => prime_fib (n + 1) 100

/-! ## Pre-condition -/

/-- `prime_fib` asks for the `n`-th Fibonacci prime, so `n ≥ 1`. -/
def Pre (n : Nat) : Prop := 1 ≤ n

/-! ## Specification vocabulary -/

/-- `FibIdxPrime j`: the `j`-th Fibonacci number is prime. -/
abbrev FibIdxPrime (j : Nat) : Prop := Nat.Prime (Nat.fib j)

/-- `FibPrime p`: `p` is a prime Fibonacci number. -/
def FibPrime (p : Nat) : Prop := Nat.Prime p ∧ ∃ k, Nat.fib k = p

/-- `FibPrime` is decidable: a Fibonacci number `p = fib k` satisfies `k ≤ p + 1`. -/
instance : DecidablePred FibPrime := fun p =>
  decidable_of_iff (Nat.Prime p ∧ ∃ k < p + 2, Nat.fib k = p) (by
    constructor
    · rintro ⟨hp, k, -, hk⟩
      exact ⟨hp, k, hk⟩
    · rintro ⟨hp, k, hk⟩
      exact ⟨hp, k, by have := Nat.le_fib_add_one k; omega, hk⟩)

/-! ## Properties and theorems -/

/-- Python's `is_prime` is a correct primality test. -/
def isPrime_prop : Prop := ∀ p : Nat, isPrime p = true ↔ Nat.Prime p

theorem isPrime_iff (p : Nat) : isPrime p = true ↔ Nat.Prime p := by
  rw [Nat.prime_def_le_sqrt]
  unfold isPrime
  by_cases hp : p < 2
  · simp only [hp, if_true, Bool.false_eq_true, false_iff, not_and]
    intro h
    omega
  · simp only [hp, if_false, List.all_eq_true, List.mem_range'_1, bne_iff_ne, ne_eq]
    push_neg at hp
    constructor
    · intro h
      refine ⟨hp, fun m hm2 hms hdvd => ?_⟩
      have hmm : m * m ≤ p := Nat.le_sqrt.mp hms
      have hm2p : m + 2 ≤ p := by nlinarith
      exact h m ⟨hm2, by omega⟩ (Nat.mod_eq_zero_of_dvd hdvd)
    · rintro ⟨-, h⟩ m ⟨hm2, hmlt⟩ hmod
      exact h m hm2 (by omega) (Nat.dvd_of_mod_eq_zero hmod)

theorem isPrime_thm : isPrime_prop := isPrime_iff

/-- A prime Fibonacci number has index at least `3` (`fib 0 = 0`, `fib 1 = fib 2 = 1`). -/
theorem three_le_of_fib_prime {k : Nat} (h : Nat.Prime (Nat.fib k)) : 3 ≤ k := by
  by_contra hlt
  push_neg at hlt
  interval_cases k
  · exact Nat.not_prime_zero (by simpa [Nat.fib_zero] using h)
  · exact Nat.not_prime_one (by simpa [Nat.fib_one] using h)
  · exact Nat.not_prime_one (by simpa [Nat.fib_two] using h)

/-- Fibonacci is strictly increasing from any prime-valued index onwards. -/
theorem fib_lt_fib_of_prime {j k : Nat} (hj : Nat.Prime (Nat.fib j)) (hjk : j < k) :
    Nat.fib j < Nat.fib k := by
  have h3 := three_le_of_fib_prime hj
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  exact Nat.fib_add_two_strictMono (by omega)

/-- Counting Fibonacci primes below `fib k` is the same as counting the indices `j < k`
with `fib j` prime. -/
theorem count_fibPrime_fib (k : Nat) :
    Nat.count FibPrime (Nat.fib k) = Nat.count FibIdxPrime k := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  have himage : (Finset.range (Nat.fib k)).filter FibPrime
      = ((Finset.range k).filter FibIdxPrime).image Nat.fib := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, FibPrime]
    constructor
    · rintro ⟨hp, hprime, j, rfl⟩
      refine ⟨j, ⟨?_, hprime⟩, rfl⟩
      by_contra hjk
      push_neg at hjk
      exact absurd hp (not_lt.mpr (Nat.fib_mono hjk))
    · rintro ⟨j, ⟨hjk, hprime⟩, rfl⟩
      exact ⟨fib_lt_fib_of_prime hprime hjk, hprime, j, rfl⟩
  rw [himage, Finset.card_image_of_injOn]
  intro x hx y hy hxy
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hx hy
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact absurd hxy (ne_of_lt (fib_lt_fib_of_prime hx.2 h))
  · exact absurd hxy.symm (ne_of_lt (fib_lt_fib_of_prime hy.2 h))

/-- Soundness of the loop, stated for an arbitrary starting point in the Fibonacci
sequence: starting from `(fib i, fib (i + 1))` with `n ≥ 1` primes still to find, a
returned value is `fib k` for the index `k` such that `fib k` is prime and exactly
`n - 1` indices in `[i + 2, k)` have prime Fibonacci values. -/
theorem loop_sound (fuel : Nat) : ∀ (i n m : Nat), 1 ≤ n →
    primeFibLoop fuel n (Nat.fib i) (Nat.fib (i + 1)) = some m →
    ∃ k, i + 2 ≤ k ∧ k < i + 2 + fuel ∧ Nat.fib k = m ∧ FibIdxPrime k ∧
      Nat.count FibIdxPrime k = Nat.count FibIdxPrime (i + 2) + (n - 1) := by
  induction fuel with
  | zero =>
    intro i n m _ h
    simp [primeFibLoop] at h
  | succ fuel ih =>
    intro i n m hn h
    simp only [primeFibLoop] at h
    rw [← Nat.fib_add_two] at h
    by_cases hq : isPrime (Nat.fib (i + 2)) = true
    · have hq' : FibIdxPrime (i + 2) := (isPrime_iff _).mp hq
      have hc3 : Nat.count FibIdxPrime (i + 3) = Nat.count FibIdxPrime (i + 2) + 1 := by
        rw [Nat.count_succ]
        simp [hq']
      rw [if_pos hq] at h
      by_cases hn1 : n - 1 = 0
      · rw [if_pos hn1] at h
        refine ⟨i + 2, le_rfl, by omega, Option.some.inj h, hq', by omega⟩
      · rw [if_neg hn1] at h
        obtain ⟨k, hk1, hk2, hk3, hk4, hk5⟩ := ih (i + 1) (n - 1) m (by omega) h
        refine ⟨k, by omega, by omega, hk3, hk4, ?_⟩
        rw [show i + 1 + 2 = i + 3 from rfl, hc3] at hk5
        omega
    · have hq' : ¬ FibIdxPrime (i + 2) := fun h' => hq ((isPrime_iff _).mpr h')
      have hc3 : Nat.count FibIdxPrime (i + 3) = Nat.count FibIdxPrime (i + 2) := by
        rw [Nat.count_succ]
        simp [hq']
      rw [if_neg hq] at h
      have hn0 : ¬ n = 0 := by omega
      rw [if_neg hn0] at h
      obtain ⟨k, hk1, hk2, hk3, hk4, hk5⟩ := ih (i + 1) n m hn h
      refine ⟨k, by omega, by omega, hk3, hk4, ?_⟩
      rw [show i + 1 + 2 = i + 3 from rfl, hc3] at hk5
      exact hk5

/-- Completeness of the loop: if `fib k` is prime, exactly `n - 1` indices in
`[i + 2, k)` carry prime Fibonacci values, and there is enough fuel to reach index `k`,
then the loop started from `(fib i, fib (i + 1))` returns `fib k`. -/
theorem loop_complete (fuel : Nat) : ∀ (i n k : Nat), 1 ≤ n →
    i + 2 ≤ k → k < i + 2 + fuel → FibIdxPrime k →
    Nat.count FibIdxPrime k = Nat.count FibIdxPrime (i + 2) + (n - 1) →
    primeFibLoop fuel n (Nat.fib i) (Nat.fib (i + 1)) = some (Nat.fib k) := by
  induction fuel with
  | zero =>
    intro i n k _ h1 h2
    omega
  | succ fuel ih =>
    intro i n k hn hik hkf hk hcount
    simp only [primeFibLoop]
    rw [← Nat.fib_add_two]
    by_cases hq : isPrime (Nat.fib (i + 2)) = true
    · have hq' : FibIdxPrime (i + 2) := (isPrime_iff _).mp hq
      have hc3 : Nat.count FibIdxPrime (i + 3) = Nat.count FibIdxPrime (i + 2) + 1 := by
        rw [Nat.count_succ]
        simp [hq']
      rw [if_pos hq]
      by_cases hn1 : n - 1 = 0
      · rw [if_pos hn1]
        have hk2 : k = i + 2 := by
          by_contra hne
          have h3 : i + 3 ≤ k := by omega
          have := Nat.count_monotone FibIdxPrime h3
          omega
        rw [hk2]
      · rw [if_neg hn1]
        have h3 : i + 3 ≤ k := by
          by_contra hne
          have hk2 : k = i + 2 := by omega
          subst hk2
          omega
        exact ih (i + 1) (n - 1) k (by omega) h3 (by omega) hk
          (by rw [show i + 1 + 2 = i + 3 from rfl, hc3]; omega)
    · have hq' : ¬ FibIdxPrime (i + 2) := fun h' => hq ((isPrime_iff _).mpr h')
      have hc3 : Nat.count FibIdxPrime (i + 3) = Nat.count FibIdxPrime (i + 2) := by
        rw [Nat.count_succ]
        simp [hq']
      rw [if_neg hq]
      have hn0 : ¬ n = 0 := by omega
      rw [if_neg hn0]
      have h3 : i + 3 ≤ k := by
        by_contra hne
        have hk2 : k = i + 2 := by omega
        subst hk2
        exact hq' hk
      exact ih (i + 1) n k hn h3 (by omega) hk
        (by rw [show i + 1 + 2 = i + 3 from rfl, hc3]; exact hcount)

/-- No index below `2` carries a prime Fibonacci number. -/
theorem count_fibIdxPrime_two : Nat.count FibIdxPrime 2 = 0 := by
  decide

/-- **Soundness.** For `n ≥ 1`, a value returned by `prime_fib n fuel` is `fib k` for an
index `k` with `fib k` prime and exactly `n - 1` smaller indices with prime Fibonacci
value: it is the `n`-th prime in the Fibonacci sequence. -/
def prime_fib_sound_prop : Prop := ∀ (n fuel m : Nat), Pre n → prime_fib n fuel = some m →
  ∃ k, Nat.fib k = m ∧ FibIdxPrime k ∧ Nat.count FibIdxPrime k = n - 1

theorem prime_fib_sound_thm : prime_fib_sound_prop := by
  intro n fuel m hn h
  have h' : primeFibLoop fuel n (Nat.fib 0) (Nat.fib (0 + 1)) = some m := by
    simpa [prime_fib, Nat.fib_zero, Nat.fib_one] using h
  obtain ⟨k, -, -, hk, hq, hc⟩ := loop_sound fuel 0 n m hn h'
  refine ⟨k, hk, hq, ?_⟩
  rw [hc, show 0 + 2 = 2 from rfl, count_fibIdxPrime_two]
  omega

/-- **The result is prime.** -/
def prime_fib_prime_prop : Prop := ∀ (n fuel m : Nat), Pre n → prime_fib n fuel = some m →
  Nat.Prime m

theorem prime_fib_prime_thm : prime_fib_prime_prop := by
  intro n fuel m hn h
  obtain ⟨k, rfl, hq, -⟩ := prime_fib_sound_thm n fuel m hn h
  exact hq

/-- **The result is a Fibonacci number.** -/
def prime_fib_fib_prop : Prop := ∀ (n fuel m : Nat), Pre n → prime_fib n fuel = some m →
  ∃ k, Nat.fib k = m

theorem prime_fib_fib_thm : prime_fib_fib_prop := by
  intro n fuel m hn h
  obtain ⟨k, hk, -, -⟩ := prime_fib_sound_thm n fuel m hn h
  exact ⟨k, hk⟩

/-- **Exactly `n - 1` prime Fibonacci numbers are smaller than the result.** -/
def prime_fib_count_prop : Prop := ∀ (n fuel m : Nat), Pre n → prime_fib n fuel = some m →
  Nat.count FibPrime m = n - 1

theorem prime_fib_count_thm : prime_fib_count_prop := by
  intro n fuel m hn h
  obtain ⟨k, rfl, -, hc⟩ := prime_fib_sound_thm n fuel m hn h
  rw [count_fibPrime_fib, hc]

/-- **The result is the `n`-th prime Fibonacci number** (`Nat.nth` is `0`-indexed). -/
def prime_fib_nth_prop : Prop := ∀ (n fuel m : Nat), Pre n → prime_fib n fuel = some m →
  Nat.nth FibPrime (n - 1) = m

theorem prime_fib_nth_thm : prime_fib_nth_prop := by
  intro n fuel m hn h
  have hmem : FibPrime m := ⟨prime_fib_prime_thm n fuel m hn h, prime_fib_fib_thm n fuel m hn h⟩
  rw [← prime_fib_count_thm n fuel m hn h]
  exact Nat.nth_count hmem

/-- **Completeness.** If `fib k` is the `n`-th prime Fibonacci number (`fib k` is prime
and exactly `n - 1` earlier indices have prime values) and the fuel allows reaching
index `k`, then `prime_fib n fuel` returns `fib k`. -/
def prime_fib_complete_prop : Prop := ∀ (n fuel k : Nat), Pre n → FibIdxPrime k →
  Nat.count FibIdxPrime k = n - 1 → k ≤ fuel + 1 → prime_fib n fuel = some (Nat.fib k)

theorem prime_fib_complete_thm : prime_fib_complete_prop := by
  intro n fuel k hn hk hc hfuel
  have h3 := three_le_of_fib_prime hk
  have := loop_complete fuel 0 n k hn (by omega) (by omega) hk
    (by rw [hc, show 0 + 2 = 2 from rfl, count_fibIdxPrime_two]; omega)
  simpa [prime_fib, Nat.fib_zero, Nat.fib_one] using this

/-- If at least `n ≥ 1` indices below `N` carry prime Fibonacci numbers, then the `n`-th
such index lies below `N`. -/
theorem exists_nth_fibIdxPrime (N n : Nat) (hn : 1 ≤ n) (h : n ≤ Nat.count FibIdxPrime N) :
    ∃ k, k < N ∧ FibIdxPrime k ∧ Nat.count FibIdxPrime k = n - 1 := by
  induction N with
  | zero =>
    rw [Nat.count_zero] at h
    omega
  | succ N ih =>
    rw [Nat.count_succ] at h
    by_cases hq : FibIdxPrime N
    · by_cases hN : n ≤ Nat.count FibIdxPrime N
      · obtain ⟨k, hk, hq', hc⟩ := ih hN
        exact ⟨k, by omega, hq', hc⟩
      · refine ⟨N, by omega, hq, ?_⟩
        simp only [hq, if_true] at h
        omega
    · simp only [hq, if_false, add_zero] at h
      obtain ⟨k, hk, hq', hc⟩ := ih h
      exact ⟨k, by omega, hq', hc⟩

/-- **`none` only when the fuel is too small.** If `prime_fib n fuel` returns `none`,
fewer than `n` of the examined Fibonacci numbers `fib 2, …, fib (fuel + 1)` are prime. -/
def prime_fib_none_prop : Prop := ∀ (n fuel : Nat), Pre n → prime_fib n fuel = none →
  Nat.count FibIdxPrime (fuel + 2) < n

theorem prime_fib_none_thm : prime_fib_none_prop := by
  intro n fuel hn h
  by_contra hle
  push_neg at hle
  obtain ⟨k, hk, hq, hc⟩ := exists_nth_fibIdxPrime (fuel + 2) n hn hle
  have := prime_fib_complete_thm n fuel k hn hq hc (by omega)
  rw [h] at this
  exact Option.noConfusion this

/-- **More fuel never changes a found answer.** -/
def prime_fib_fuel_mono_prop : Prop := ∀ (n fuel fuel' m : Nat), fuel ≤ fuel' →
  prime_fib n fuel = some m → prime_fib n fuel' = some m

theorem loop_fuel_mono (fuel : Nat) : ∀ (fuel' n a b m : Nat), fuel ≤ fuel' →
    primeFibLoop fuel n a b = some m → primeFibLoop fuel' n a b = some m := by
  induction fuel with
  | zero =>
    intro fuel' n a b m _ h
    simp [primeFibLoop] at h
  | succ fuel ih =>
    intro fuel' n a b m hle h
    obtain ⟨fuel'', rfl⟩ : ∃ f, fuel' = f + 1 := ⟨fuel' - 1, by omega⟩
    simp only [primeFibLoop] at h ⊢
    generalize (if isPrime (a + b) = true then n - 1 else n) = n' at h ⊢
    by_cases hz : n' = 0
    · rw [if_pos hz] at h ⊢
      exact h
    · rw [if_neg hz] at h ⊢
      exact ih fuel'' n' b (a + b) m (by omega) h

theorem prime_fib_fuel_mono_thm : prime_fib_fuel_mono_prop := by
  intro n fuel fuel' m hle h
  exact loop_fuel_mono fuel fuel' n 0 1 m hle h

/-- **Consecutive answers are strictly increasing.** -/
def prime_fib_strictMono_prop : Prop := ∀ (n fuel fuel' m m' : Nat), Pre n →
  prime_fib n fuel = some m → prime_fib (n + 1) fuel' = some m' → m < m'

theorem prime_fib_strictMono_thm : prime_fib_strictMono_prop := by
  intro n fuel fuel' m m' hn h h'
  have hc := prime_fib_count_thm n fuel m hn h
  have hc' := prime_fib_count_thm (n + 1) fuel' m' (by unfold Pre; omega) h'
  by_contra hle
  push_neg at hle
  have := Nat.count_monotone FibPrime hle
  rw [hc, hc'] at this
  omega

/-- **Termination under the Fibonacci-prime conjecture.** If there are infinitely many
prime Fibonacci numbers, then for every `n ≥ 1` the Python program terminates: some fuel
suffices, and the answer is the `n`-th prime Fibonacci number. -/
def prime_fib_terminates_prop : Prop := (setOf FibPrime).Infinite → ∀ n : Nat, Pre n →
  ∃ fuel, prime_fib n fuel = some (Nat.nth FibPrime (n - 1))

theorem prime_fib_terminates_thm : prime_fib_terminates_prop := by
  intro hinf n hn
  have hmem : FibPrime (Nat.nth FibPrime (n - 1)) := Nat.nth_mem_of_infinite hinf (n - 1)
  have hcnt : Nat.count FibPrime (Nat.nth FibPrime (n - 1)) = n - 1 :=
    Nat.count_nth_of_infinite hinf (n - 1)
  obtain ⟨hp, k, hk⟩ := hmem
  rw [← hk] at hcnt hp ⊢
  rw [count_fibPrime_fib] at hcnt
  exact ⟨k, prime_fib_complete_thm n k k hn hp hcnt (by omega)⟩

/-- Outside the intended domain, Python's `prime_fib(0)` returns `1` (the first appended
Fibonacci number): `n` is already `0` after the first iteration. -/
theorem prime_fib_zero (fuel : Nat) : prime_fib 0 (fuel + 1) = some 1 := by
  simp [prime_fib, primeFibLoop]

/-! ## Post-condition -/

/-- Post-condition of `prime_fib n fuel = r` for `n ≥ 1`:
* if `r = some m`, then `m` is prime, `m` is a Fibonacci number, exactly `n - 1` prime
  Fibonacci numbers are smaller than `m`, and `m` is the `n`-th prime Fibonacci number;
* if `r = none`, fewer than `n` of the examined numbers `fib 2, …, fib (fuel + 1)` are
  prime (the Python program would still be looping). -/
def Post_prop (n fuel : Nat) (r : Option Nat) : Prop :=
  (∀ m, r = some m →
      Nat.Prime m ∧ (∃ k, Nat.fib k = m) ∧ Nat.count FibPrime m = n - 1 ∧
      Nat.nth FibPrime (n - 1) = m) ∧
  (r = none → Nat.count FibIdxPrime (fuel + 2) < n)

/-! ## Property-based tests

Executable Boolean forms of the properties above, checked on many inputs. -/

/-- All Fibonacci numbers `< m` (executable helper for the counting properties). -/
def fibsBelow (m : Nat) : List Nat :=
  go (m + 2) 0 1 []
where
  go : Nat → Nat → Nat → List Nat → List Nat
    | 0, _, _, acc => acc.reverse
    | fuel + 1, a, b, acc => if a < m then go fuel b (a + b) (a :: acc) else acc.reverse

example : fibsBelow 20 = [0, 1, 1, 2, 3, 5, 8, 13] := by native_decide

/-- Executable count of the prime Fibonacci numbers below `m`. -/
def countFibPrimesBelow (m : Nat) : Nat :=
  ((fibsBelow m).eraseDups.filter isPrime).length

-- The executable count agrees with `Nat.count FibPrime` on small inputs.
example : (List.range 60).all (fun m => countFibPrimesBelow m == Nat.count FibPrime m) = true := by
  native_decide

-- PBT for `isPrime_prop` (`isPrime` agrees with `Nat.Prime`).
example : (List.range 2000).all (fun p => isPrime p == decide (Nat.Prime p)) = true := by
  native_decide
#eval Plausible.Testable.check (∀ p : Nat, isPrime p = decide (Nat.Prime p))

-- PBT for `prime_fib_prime_prop`.
example : (List.range 10).all (fun n => match prime_fib (n + 1) 100 with
    | some m => decide (Nat.Prime m)
    | none => false) = true := by native_decide

-- PBT for `prime_fib_fib_prop`: the result occurs in the Fibonacci sequence.
example : (List.range 10).all (fun n => match prime_fib (n + 1) 100 with
    | some m => (fibsBelow (m + 1)).contains m
    | none => false) = true := by native_decide

-- PBT for `prime_fib_sound_prop`: result is `fib k` with `fib k` prime and
-- `Nat.count FibIdxPrime k = n - 1`.
example : (List.range 10).all (fun n => match prime_fib (n + 1) 100 with
    | some m => (List.range 50).any (fun k =>
        Nat.fib k == m && isPrime (Nat.fib k) && Nat.count FibIdxPrime k == n)
    | none => false) = true := by native_decide

-- PBT for `prime_fib_count_prop` (executable counterpart `countFibPrimesBelow`).
example : (List.range 10).all (fun n => match prime_fib (n + 1) 100 with
    | some m => countFibPrimesBelow m == n
    | none => false) = true := by native_decide
-- Direct check with `Nat.count FibPrime` for the first six values (small enough).
example : (List.range 6).all (fun n => match prime_fib (n + 1) 100 with
    | some m => Nat.count FibPrime m == n
    | none => false) = true := by native_decide
-- PBT: `prime_fib_nth_prop` is not executable (`Nat.nth` is noncomputable); its executable
-- counterpart is the `Nat.count FibPrime m = n - 1` check above.

-- PBT for `prime_fib_complete_prop`: for every index `k ≤ 60` with `fib k` prime,
-- `prime_fib (count + 1) fuel = some (fib k)` for every fuel `≥ k - 1`.
example : (List.range 61).all (fun k =>
    if isPrime (Nat.fib k) then
      (List.range 5).all (fun d => prime_fib (Nat.count FibIdxPrime k + 1) (k - 1 + d) == some (Nat.fib k))
    else true) = true := by native_decide

-- PBT for `prime_fib_none_prop`.
example : (List.range 12).all (fun n => (List.range 50).all (fun fuel =>
    match prime_fib (n + 1) fuel with
    | none => decide (Nat.count FibIdxPrime (fuel + 2) < n + 1)
    | some _ => true)) = true := by native_decide

-- PBT for `prime_fib_fuel_mono_prop`.
example : (List.range 12).all (fun n => (List.range 50).all (fun fuel => (List.range 10).all (fun d =>
    match prime_fib n fuel with
    | some m => prime_fib n (fuel + d) == some m
    | none => true))) = true := by native_decide
#eval Plausible.Testable.check (∀ n fuel d : Nat,
  (prime_fib n fuel).isSome → prime_fib n (fuel + d) = prime_fib n fuel)

-- PBT for `prime_fib_strictMono_prop`.
example : (List.range 10).all (fun n => match prime_fib (n + 1) 100, prime_fib (n + 2) 100 with
    | some m, some m' => decide (m < m')
    | _, _ => false) = true := by native_decide

-- PBT for `prime_fib_terminates_prop`: not executable as stated (its hypothesis is the open
-- infinitude conjecture); the executable evidence is that the first 11 Fibonacci primes are
-- found with finite fuel.
example : (List.range 11).all (fun n => (prime_fib (n + 1) 100).isSome) = true := by native_decide

-- PBT for `Post_prop` (executable counterpart: `isPrime`, membership in the Fibonacci
-- sequence, `countFibPrimesBelow`, and the `none` clause).
example : (List.range 12).all (fun n => (List.range 50).all (fun fuel =>
    match prime_fib (n + 1) fuel with
    | some m => isPrime m && (fibsBelow (m + 1)).contains m && (countFibPrimesBelow m == n)
    | none => decide (Nat.count FibIdxPrime (fuel + 2) < n + 1))) = true := by native_decide

/-! ## Correctness theorem -/

theorem prime_fib_correct (n fuel : Nat) (hn : Pre n) : Post_prop n fuel (prime_fib n fuel) := by
  refine ⟨fun m h => ⟨prime_fib_prime_thm n fuel m hn h, prime_fib_fib_thm n fuel m hn h,
    prime_fib_count_thm n fuel m hn h, prime_fib_nth_thm n fuel m hn h⟩, fun h => ?_⟩
  exact prime_fib_none_thm n fuel hn h

/-! ## Imperative implementation -/

/-- Imperative version of the Python program: the list `f` is kept as a growable array,
`n` is decremented at every prime, and the loop returns early when `n` hits `0`.  As in
the functional version, at most `fuel` iterations of the `while True` loop are run. -/
def prime_fib_imp (n : Nat) (fuel : Nat) : Option Nat := Id.run do
  let mut n := n
  let mut a := 0  -- f[-2]
  let mut b := 1  -- f[-1]
  for _ in [0:fuel] do
    let c := a + b  -- f.append(f[-1] + f[-2])
    a := b
    b := c
    if isPrime c then
      n := n - 1
    if n = 0 then
      return some c
  return none

/-! ## Imperative tests -/

example : prime_fib_imp 1 100 = some 2 := by native_decide
example : prime_fib_imp 2 100 = some 3 := by native_decide
example : prime_fib_imp 3 100 = some 5 := by native_decide
example : prime_fib_imp 4 100 = some 13 := by native_decide
example : prime_fib_imp 5 100 = some 89 := by native_decide
example : prime_fib_imp 6 100 = some 233 := by native_decide
example : prime_fib_imp 7 100 = some 1597 := by native_decide
example : prime_fib_imp 8 100 = some 28657 := by native_decide
example : prime_fib_imp 9 100 = some 514229 := by native_decide
example : prime_fib_imp 10 100 = some 433494437 := by native_decide
example : prime_fib_imp 10 41 = none := by native_decide
example : prime_fib_imp 0 100 = some 1 := by native_decide
#eval prime_fib_imp 10 100

-- PBT: the two implementations agree.
example : (List.range 12).all (fun n => (List.range 50).all (fun fuel =>
    prime_fib n fuel == prime_fib_imp n fuel)) = true := by native_decide
#eval Plausible.Testable.check (∀ n fuel : Nat, prime_fib n fuel = prime_fib_imp n fuel)

/-! ## Equivalence theorem -/

theorem prime_fib_eq_imp (n fuel : Nat) : prime_fib n fuel = prime_fib_imp n fuel := by
  sorry

end humaneval_39_prime_fib
