import Mathlib

/-!
# HumanEval/39 — `prime_fib`

`prime_fib n` returns the `n`-th number (1-indexed) that is both a Fibonacci number and a prime:

```
prime_fib(1) = 2,  prime_fib(2) = 3,  prime_fib(3) = 5,  prime_fib(4) = 13,  prime_fib(5) = 89,
prime_fib(6) = 233, prime_fib(7) = 1597, prime_fib(8) = 28657, prime_fib(9) = 514229,
prime_fib(10) = 433494437
```

The Python reference keeps the running list `f = [0, 1]`, repeatedly appends `f[-1] + f[-2]`
(so the appended values are `Nat.fib 2, Nat.fib 3, Nat.fib 4, …`), decrements a counter `n`
whenever the freshly appended value passes the trial-division test `is_prime`, and returns that
value as soon as the counter reaches `0`.

## Modelling notes

* The program is entirely discrete (`int` arithmetic only), so the whole formalisation lives on
  `Nat`.  Python's `math.sqrt` is used only to bound the trial division; `Nat.sqrt` is its exact
  integer counterpart, and `isPrimeNat` below reproduces the same candidate set.
* `countPrimeFib m` counts the indices `i ≤ m` for which `Nat.fib i` is prime.  It is the exact
  counterpart of "how many times the Python loop has decremented `n` once `f` has grown to
  `[fib 0, …, fib m]`", and it is what makes the statement "`v` is the `n`-th prime Fibonacci
  number" precise.
* The Python `while True` loop carries no fuel: it stops as soon as `n` prime Fibonacci numbers
  have been produced.  That this happens for *every* `n` is equivalent to "there are infinitely
  many prime Fibonacci numbers", which is an open problem.  The Lean implementation therefore
  carries an explicit horizon `fuelOf n` and returns `0` if the horizon is exhausted; `Pre n`
  records `0 < n` together with the fact that the search did succeed.  This is the maximal
  honestly describable domain of the reference program, not a narrowing of it: for every `n` for
  which the Python loop terminates with a value, `Pre n` holds (the horizon is far above the index
  of the `n`-th prime Fibonacci number for every `n` that is known to exist).
-/

namespace humaneval_39_prime_fib

open Nat List

/-!
## 1. Functional implementation
-/

/-- `isPrimeNat p` is the Lean counterpart of the Python helper `is_prime`: `false` for `p < 2`,
otherwise trial division of `p` by every candidate `k` with `2 ≤ k ≤ √p`.  The Python loop runs
over `range(2, min(int(math.sqrt(p)) + 1, p - 1))`, i.e. over `2, …, ⌊√p⌋` for `p ≥ 4` and over
the empty range for `p ∈ {2, 3}`; `List.range (Nat.sqrt p + 1)` covers exactly the same
candidates, the spurious small ones being rejected by the `2 ≤ k` guard. -/
def isPrimeNat (p : Nat) : Bool :=
  if p < 2 then false
  else (List.range (Nat.sqrt p + 1)).all (fun k => decide (2 ≤ k → p % k ≠ 0))

@[simp] theorem isPrimeNat_of_lt_two {p : Nat} (h : p < 2) : isPrimeNat p = false := by
  simp [isPrimeNat, h]

theorem isPrimeNat_of_ge_two {p : Nat} (h : 2 ≤ p) :
    isPrimeNat p = (List.range (Nat.sqrt p + 1)).all (fun k => decide (2 ≤ k → p % k ≠ 0)) := by
  simp [isPrimeNat, Nat.not_lt_of_ge h]

/-- The trial-division test is correct: it agrees with the mathematical notion of primality. -/
theorem isPrimeNat_true_iff {p : Nat} : isPrimeNat p = true ↔ Nat.Prime p := by
  constructor
  · intro h
    by_cases h2 : p < 2
    · simp [isPrimeNat, h2] at h
    · have hp2 : 2 ≤ p := Nat.le_of_not_lt h2
      rw [isPrimeNat_of_ge_two hp2, List.all_eq_true] at h
      rw [Nat.prime_def_minFac]
      refine ⟨hp2, ?_⟩
      by_contra hne
      have hdvd : p.minFac ∣ p := Nat.minFac_dvd p
      have hmp : Nat.Prime p.minFac := Nat.minFac_prime (by omega)
      have hm2 : 2 ≤ p.minFac := Nat.Prime.two_le hmp
      have hmlt : p.minFac < p := Nat.lt_of_le_of_ne (Nat.minFac_le (by omega)) hne
      have hq : p.minFac * (p / p.minFac) = p := Nat.mul_div_cancel' hdvd
      have hq0 : p / p.minFac ≠ 0 := by
        intro h0
        rw [h0] at hq
        simp at hq
        omega
      have hq1 : p / p.minFac ≠ 1 := by
        intro h1
        rw [h1] at hq
        simp at hq
        exact hne hq
      have hq2 : 2 ≤ p / p.minFac := by
        by_contra hlt
        have hle : p / p.minFac ≤ 1 := Nat.lt_succ_iff.mp (Nat.lt_of_not_le hlt)
        interval_cases p / p.minFac
        · exact hq0 rfl
        · exact hq1 rfl
      have hle : p.minFac ≤ p / p.minFac :=
        Nat.minFac_le_of_dvd hq2 (Nat.div_dvd_of_dvd hdvd)
      have hsqrt : p.minFac ≤ Nat.sqrt p := by
        rw [Nat.le_sqrt]
        exact le_trans (Nat.mul_le_mul_left _ hle) (le_of_eq hq)
      have hmem : p.minFac ∈ List.range (Nat.sqrt p + 1) := by
        rw [List.mem_range]
        exact Nat.lt_succ_of_le hsqrt
      have hk := h (p.minFac) hmem
      rw [decide_eq_true_iff] at hk
      exact (hk hm2) (Nat.mod_eq_zero_of_dvd hdvd)
  · intro hprime
    have hp2 : 2 ≤ p := Nat.Prime.two_le hprime
    rw [isPrimeNat_of_ge_two hp2, List.all_eq_true]
    intro k hk
    rw [decide_eq_true_iff]
    intro hk2 hmod
    have hdvd : k ∣ p := Nat.dvd_of_mod_eq_zero hmod
    have heq := hprime.eq_one_or_self_of_dvd k hdvd
    have hklt : k ≤ Nat.sqrt p := Nat.lt_succ_iff.mp (List.mem_range.mp hk)
    have hsqrtlt : Nat.sqrt p < p := Nat.sqrt_lt_self (by omega)
    omega

/-- `isPrimeNat p = false` exactly when `p` is not prime. -/
theorem isPrimeNat_false_iff {p : Nat} : isPrimeNat p = false ↔ ¬ Nat.Prime p := by
  have hor : isPrimeNat p = true ∨ isPrimeNat p = false := by
    cases hb : isPrimeNat p <;> simp
  constructor
  · intro h1 hp
    rw [← isPrimeNat_true_iff] at hp
    rw [h1] at hp
    exact Bool.noConfusion hp
  · intro hnp
    rcases hor with h1 | h1
    · exact absurd (isPrimeNat_true_iff.mp h1) hnp
    · exact h1

/-- Fidelity of the trial-division bound: for `p ≥ 4` one has `⌊√p⌋ + 1 ≤ p - 1`, so the Python
bound `min(int(math.sqrt(p)) + 1, p - 1)` is `⌊√p⌋ + 1` and the Python loop
`for k in range(2, min(int(math.sqrt(p)) + 1, p - 1))` runs over exactly the candidates
`2, …, ⌊√p⌋` — the candidates `isPrimeNat` tests (its extra range entries `0, 1` are rejected by
the `2 ≤ k` guard, and for `p ∈ {2, 3}` both versions test nothing). -/
theorem python_sqrt_bound {p : Nat} (h : 4 ≤ p) : Nat.sqrt p + 1 ≤ p - 1 := by
  have h1 : Nat.sqrt p < p - 1 := by
    rw [Nat.sqrt_lt]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 4 := ⟨p - 4, by omega⟩
    have hsub : q + 4 - 1 = q + 3 := by omega
    rw [hsub]
    have h5 : (q + 3) * (q + 3) = q * q + 6 * q + 9 := by ring
    rw [h5]
    have h6 : 0 ≤ q * q := Nat.zero_le _
    omega
  omega

theorem python_min_bound {p : Nat} (h : 4 ≤ p) :
    min (Nat.sqrt p + 1) (p - 1) = Nat.sqrt p + 1 :=
  min_eq_left (python_sqrt_bound h)

/-- The Python loop `for k in range(2, min(int(math.sqrt(p)) + 1, p - 1))` iterates over
`2, …, ⌊√p⌋` for every `p ≥ 4`. -/
theorem python_range_eq {p : Nat} (h : 4 ≤ p) :
    List.range' 2 (min (Nat.sqrt p + 1) (p - 1) - 2) = List.range' 2 (Nat.sqrt p - 1) := by
  rw [python_min_bound h]
  have h2 : 2 ≤ Nat.sqrt p := Nat.le_sqrt.mpr (by nlinarith)
  have h3 : Nat.sqrt p + 1 - 2 = Nat.sqrt p - 1 := by omega
  rw [h3]

/-- `countPrimeFib m` is the number of indices `i ≤ m` such that `Nat.fib i` is prime, i.e. the
number of prime Fibonacci numbers among `fib 0, …, fib m`.  It counts exactly how often the
Python loop decrements `n` while the list `f` grows to `[fib 0, …, fib m]`. -/
def countPrimeFib : Nat → Nat
  | 0 => 0
  | 1 => 0
  | m + 2 => countPrimeFib (m + 1) + if Nat.Prime (Nat.fib (m + 2)) then 1 else 0

@[simp] theorem countPrimeFib_zero : countPrimeFib 0 = 0 := rfl
@[simp] theorem countPrimeFib_one : countPrimeFib 1 = 0 := rfl

theorem countPrimeFib_add_two (m : Nat) :
    countPrimeFib (m + 2) =
      countPrimeFib (m + 1) + if Nat.Prime (Nat.fib (m + 2)) then 1 else 0 := rfl

theorem countPrimeFib_succ (j : Nat) :
    countPrimeFib (j + 1) =
      countPrimeFib j + if Nat.Prime (Nat.fib (j + 1)) then 1 else 0 := by
  cases j with
  | zero => simp [Nat.fib_one, Nat.not_prime_one]
  | succ m =>
      have h : m + 1 + 1 = m + 2 := by omega
      rw [h]
      exact countPrimeFib_add_two m

theorem countPrimeFib_le_succ (a : Nat) : countPrimeFib a ≤ countPrimeFib (a + 1) := by
  have e := countPrimeFib_succ a
  have h : 0 ≤ (if Nat.Prime (Nat.fib (a + 1)) then 1 else 0) := by split <;> omega
  omega

theorem countPrimeFib_mono : ∀ {a b : Nat}, a ≤ b → countPrimeFib a ≤ countPrimeFib b := by
  intro a b h
  have key : ∀ k : Nat, countPrimeFib a ≤ countPrimeFib (a + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have e : a + (k + 1) = (a + k) + 1 := by omega
        rw [e]
        exact le_trans ih (countPrimeFib_le_succ (a + k))
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  rw [hk]
  exact key k

theorem countPrimeFib_succ_prime {m : Nat} (hm : 0 < m) (h : Nat.Prime (Nat.fib m)) :
    countPrimeFib m = countPrimeFib (m - 1) + 1 := by
  have h1 : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have e := countPrimeFib_succ (m - 1)
  rw [h1] at e
  rw [e, if_pos h]

/-- Search horizon for the Python `while True` loop.  Every iteration appends one Fibonacci
number, so `fuelOf n` iterations inspect `Nat.fib 2, …, Nat.fib (fuelOf n + 1)`.  The `n`-th
prime Fibonacci number has index `43` for `n = 10` and index `569` for the largest one currently
known (`n = 26`), so `50 * (n + 2)` is a generous horizon for every `n` in the tested range. -/
def fuelOf (n : Nat) : Nat := 50 * (n + 2)

/-- `primeFibAux fuel a b n` is the Python loop, where `a` and `b` are the last two entries of the
list `f` (`a = f[-2]`, `b = f[-1]`), `n` is the number of prime Fibonacci numbers that still have
to be found, and `fuel` bounds the number of remaining iterations.  One iteration appends `a + b`,
decrements `n` when `a + b` is prime, and returns `a + b` as soon as the counter reaches `0`.
`0` signals that the horizon was exhausted first. -/
def primeFibAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | fuel + 1, a, b, n =>
      let v := a + b
      let n' := if isPrimeNat v then n - 1 else n
      if n' = 0 then v else primeFibAux fuel b v n'

@[simp] theorem primeFibAux_zero_fuel (a b n : Nat) : primeFibAux 0 a b n = 0 := rfl

theorem primeFibAux_succ (fuel a b n : Nat) :
    primeFibAux (fuel + 1) a b n =
      (if (if isPrimeNat (a + b) = true then n - 1 else n) = 0 then a + b
       else primeFibAux fuel b (a + b) (if isPrimeNat (a + b) = true then n - 1 else n)) := by
  simp only [primeFibAux]

/-- One iteration in which the appended value is not prime: the counter is unchanged. -/
theorem primeFibAux_step_notprime (fuel a b n v : Nat) (hv : a + b = v)
    (h : isPrimeNat v = false) (hn : 1 ≤ n) :
    primeFibAux (fuel + 1) a b n = primeFibAux fuel b v n := by
  have h1 : (if isPrimeNat (a + b) = true then n - 1 else n) = n := by
    rw [hv, h]; simp
  have h2 : n ≠ 0 := by omega
  rw [primeFibAux_succ, h1, if_neg h2, hv]

/-- One iteration in which the appended value is prime but more are still needed. -/
theorem primeFibAux_step_prime (fuel a b n v : Nat) (hv : a + b = v)
    (h : isPrimeNat v = true) (hn : 2 ≤ n) :
    primeFibAux (fuel + 1) a b n = primeFibAux fuel b v (n - 1) := by
  have h1 : (if isPrimeNat (a + b) = true then n - 1 else n) = n - 1 := by
    rw [hv, h]; simp
  have h2 : n - 1 ≠ 0 := by omega
  rw [primeFibAux_succ, h1, if_neg h2, hv]

/-- The terminating iteration: the appended value is prime and the counter drops to `0`. -/
theorem primeFibAux_step_last (fuel a b v : Nat) (hv : a + b = v)
    (h : isPrimeNat v = true) :
    primeFibAux (fuel + 1) a b 1 = v := by
  have h1 : (if isPrimeNat (a + b) = true then 1 - 1 else 1) = 0 := by
    rw [hv, h]; simp
  rw [primeFibAux_succ, h1, if_pos rfl, hv]

/-- The Python loop body runs once before the `n == 0` test, so `prime_fib(0)` returns the first
appended value `fib 2 = 1`. -/
theorem primeFibAux_step_zero (fuel a b v : Nat) (hv : a + b = v) :
    primeFibAux (fuel + 1) a b 0 = v := by
  have h1 : (if isPrimeNat (a + b) = true then 0 - 1 else 0) = 0 := by
    split <;> simp
  rw [primeFibAux_succ, h1, if_pos rfl, hv]

/-- `primeFib n` is the `n`-th number that is both a Fibonacci number and a prime: the Lean
counterpart of `prime_fib(n)`, started with `f = [0, 1]`, i.e. `a = Nat.fib 0 = 0` and
`b = Nat.fib 1 = 1`. -/
def primeFib (n : Nat) : Nat := primeFibAux (fuelOf n) 0 1 n

theorem primeFib_zero : primeFib 0 = 1 :=
  primeFibAux_step_zero 99 0 1 1 rfl

/-!
## 2. Unit tests

Grounded tests for the ten values asserted by the Python `check` function (plus `n = 0`, where the
Python loop body runs once before the `n == 0` test and hence returns `fib 2 = 1`).
-/

example : primeFib 0 = 1 := by native_decide
example : primeFib 1 = 2 := by native_decide
example : primeFib 2 = 3 := by native_decide
example : primeFib 3 = 5 := by native_decide
example : primeFib 4 = 13 := by native_decide
example : primeFib 5 = 89 := by native_decide
example : primeFib 6 = 233 := by native_decide
example : primeFib 7 = 1597 := by native_decide
example : primeFib 8 = 28657 := by native_decide
example : primeFib 9 = 514229 := by native_decide
example : primeFib 10 = 433494437 := by native_decide

#eval primeFib 1
#eval primeFib 5
#eval primeFib 10

/-!
### Kernel-checked values

The ten values asserted by the Python `check` function, this time proved by the Lean kernel
(no `native_decide`): every iteration of the loop is justified by one of the step lemmas
above, and the primality of each appended Fibonacci number is certified by `norm_num`
through `isPrimeNat_true_iff` / `isPrimeNat_false_iff`. -/

theorem isPrimeNat_val_1 : isPrimeNat 1 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_2 : isPrimeNat 2 = true := isPrimeNat_true_iff.mpr (by norm_num)
theorem isPrimeNat_val_3 : isPrimeNat 3 = true := isPrimeNat_true_iff.mpr (by norm_num)
theorem isPrimeNat_val_5 : isPrimeNat 5 = true := isPrimeNat_true_iff.mpr (by norm_num)
theorem isPrimeNat_val_8 : isPrimeNat 8 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_13 : isPrimeNat 13 = true := isPrimeNat_true_iff.mpr (by norm_num)
theorem isPrimeNat_val_21 : isPrimeNat 21 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_34 : isPrimeNat 34 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_55 : isPrimeNat 55 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_89 : isPrimeNat 89 = true := isPrimeNat_true_iff.mpr (by norm_num)
theorem isPrimeNat_val_144 : isPrimeNat 144 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_233 : isPrimeNat 233 = true := isPrimeNat_true_iff.mpr (by norm_num)
theorem isPrimeNat_val_377 : isPrimeNat 377 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_610 : isPrimeNat 610 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_987 : isPrimeNat 987 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_1597 : isPrimeNat 1597 = true := isPrimeNat_true_iff.mpr (by norm_num)
theorem isPrimeNat_val_2584 : isPrimeNat 2584 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_4181 : isPrimeNat 4181 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_6765 : isPrimeNat 6765 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_10946 : isPrimeNat 10946 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_17711 : isPrimeNat 17711 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_28657 : isPrimeNat 28657 = true := isPrimeNat_true_iff.mpr (by norm_num)
theorem isPrimeNat_val_46368 : isPrimeNat 46368 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_75025 : isPrimeNat 75025 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_121393 : isPrimeNat 121393 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_196418 : isPrimeNat 196418 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_317811 : isPrimeNat 317811 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_514229 : isPrimeNat 514229 = true := isPrimeNat_true_iff.mpr (by norm_num)
theorem isPrimeNat_val_832040 : isPrimeNat 832040 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_1346269 : isPrimeNat 1346269 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_2178309 : isPrimeNat 2178309 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_3524578 : isPrimeNat 3524578 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_5702887 : isPrimeNat 5702887 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_9227465 : isPrimeNat 9227465 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_14930352 : isPrimeNat 14930352 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_24157817 : isPrimeNat 24157817 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_39088169 : isPrimeNat 39088169 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_63245986 : isPrimeNat 63245986 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_102334155 : isPrimeNat 102334155 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_165580141 : isPrimeNat 165580141 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_267914296 : isPrimeNat 267914296 = false := isPrimeNat_false_iff.mpr (by norm_num)
theorem isPrimeNat_val_433494437 : isPrimeNat 433494437 = true := isPrimeNat_true_iff.mpr (by norm_num)

theorem primeFib_one : primeFib 1 = 2 := by
  calc primeFib 1 = primeFibAux 150 0 1 1 := by rfl
    _ = primeFibAux 149 1 1 1 := by rw [primeFibAux_step_notprime 149 0 1 1 1 rfl isPrimeNat_val_1 (by omega)]
    _ = 2 := by rw [primeFibAux_step_last 148 1 1 2 rfl isPrimeNat_val_2]

theorem primeFib_two : primeFib 2 = 3 := by
  calc primeFib 2 = primeFibAux 200 0 1 2 := by rfl
    _ = primeFibAux 199 1 1 2 := by rw [primeFibAux_step_notprime 199 0 1 2 1 rfl isPrimeNat_val_1 (by omega)]
    _ = primeFibAux 198 1 2 1 := by rw [primeFibAux_step_prime 198 1 1 2 2 rfl isPrimeNat_val_2 (by omega)]
    _ = 3 := by rw [primeFibAux_step_last 197 1 2 3 rfl isPrimeNat_val_3]

theorem primeFib_three : primeFib 3 = 5 := by
  calc primeFib 3 = primeFibAux 250 0 1 3 := by rfl
    _ = primeFibAux 249 1 1 3 := by rw [primeFibAux_step_notprime 249 0 1 3 1 rfl isPrimeNat_val_1 (by omega)]
    _ = primeFibAux 248 1 2 2 := by rw [primeFibAux_step_prime 248 1 1 3 2 rfl isPrimeNat_val_2 (by omega)]
    _ = primeFibAux 247 2 3 1 := by rw [primeFibAux_step_prime 247 1 2 2 3 rfl isPrimeNat_val_3 (by omega)]
    _ = 5 := by rw [primeFibAux_step_last 246 2 3 5 rfl isPrimeNat_val_5]

theorem primeFib_four : primeFib 4 = 13 := by
  calc primeFib 4 = primeFibAux 300 0 1 4 := by rfl
    _ = primeFibAux 299 1 1 4 := by rw [primeFibAux_step_notprime 299 0 1 4 1 rfl isPrimeNat_val_1 (by omega)]
    _ = primeFibAux 298 1 2 3 := by rw [primeFibAux_step_prime 298 1 1 4 2 rfl isPrimeNat_val_2 (by omega)]
    _ = primeFibAux 297 2 3 2 := by rw [primeFibAux_step_prime 297 1 2 3 3 rfl isPrimeNat_val_3 (by omega)]
    _ = primeFibAux 296 3 5 1 := by rw [primeFibAux_step_prime 296 2 3 2 5 rfl isPrimeNat_val_5 (by omega)]
    _ = primeFibAux 295 5 8 1 := by rw [primeFibAux_step_notprime 295 3 5 1 8 rfl isPrimeNat_val_8 (by omega)]
    _ = 13 := by rw [primeFibAux_step_last 294 5 8 13 rfl isPrimeNat_val_13]

theorem primeFib_five : primeFib 5 = 89 := by
  calc primeFib 5 = primeFibAux 350 0 1 5 := by rfl
    _ = primeFibAux 349 1 1 5 := by rw [primeFibAux_step_notprime 349 0 1 5 1 rfl isPrimeNat_val_1 (by omega)]
    _ = primeFibAux 348 1 2 4 := by rw [primeFibAux_step_prime 348 1 1 5 2 rfl isPrimeNat_val_2 (by omega)]
    _ = primeFibAux 347 2 3 3 := by rw [primeFibAux_step_prime 347 1 2 4 3 rfl isPrimeNat_val_3 (by omega)]
    _ = primeFibAux 346 3 5 2 := by rw [primeFibAux_step_prime 346 2 3 3 5 rfl isPrimeNat_val_5 (by omega)]
    _ = primeFibAux 345 5 8 2 := by rw [primeFibAux_step_notprime 345 3 5 2 8 rfl isPrimeNat_val_8 (by omega)]
    _ = primeFibAux 344 8 13 1 := by rw [primeFibAux_step_prime 344 5 8 2 13 rfl isPrimeNat_val_13 (by omega)]
    _ = primeFibAux 343 13 21 1 := by rw [primeFibAux_step_notprime 343 8 13 1 21 rfl isPrimeNat_val_21 (by omega)]
    _ = primeFibAux 342 21 34 1 := by rw [primeFibAux_step_notprime 342 13 21 1 34 rfl isPrimeNat_val_34 (by omega)]
    _ = primeFibAux 341 34 55 1 := by rw [primeFibAux_step_notprime 341 21 34 1 55 rfl isPrimeNat_val_55 (by omega)]
    _ = 89 := by rw [primeFibAux_step_last 340 34 55 89 rfl isPrimeNat_val_89]

theorem primeFib_six : primeFib 6 = 233 := by
  calc primeFib 6 = primeFibAux 400 0 1 6 := by rfl
    _ = primeFibAux 399 1 1 6 := by rw [primeFibAux_step_notprime 399 0 1 6 1 rfl isPrimeNat_val_1 (by omega)]
    _ = primeFibAux 398 1 2 5 := by rw [primeFibAux_step_prime 398 1 1 6 2 rfl isPrimeNat_val_2 (by omega)]
    _ = primeFibAux 397 2 3 4 := by rw [primeFibAux_step_prime 397 1 2 5 3 rfl isPrimeNat_val_3 (by omega)]
    _ = primeFibAux 396 3 5 3 := by rw [primeFibAux_step_prime 396 2 3 4 5 rfl isPrimeNat_val_5 (by omega)]
    _ = primeFibAux 395 5 8 3 := by rw [primeFibAux_step_notprime 395 3 5 3 8 rfl isPrimeNat_val_8 (by omega)]
    _ = primeFibAux 394 8 13 2 := by rw [primeFibAux_step_prime 394 5 8 3 13 rfl isPrimeNat_val_13 (by omega)]
    _ = primeFibAux 393 13 21 2 := by rw [primeFibAux_step_notprime 393 8 13 2 21 rfl isPrimeNat_val_21 (by omega)]
    _ = primeFibAux 392 21 34 2 := by rw [primeFibAux_step_notprime 392 13 21 2 34 rfl isPrimeNat_val_34 (by omega)]
    _ = primeFibAux 391 34 55 2 := by rw [primeFibAux_step_notprime 391 21 34 2 55 rfl isPrimeNat_val_55 (by omega)]
    _ = primeFibAux 390 55 89 1 := by rw [primeFibAux_step_prime 390 34 55 2 89 rfl isPrimeNat_val_89 (by omega)]
    _ = primeFibAux 389 89 144 1 := by rw [primeFibAux_step_notprime 389 55 89 1 144 rfl isPrimeNat_val_144 (by omega)]
    _ = 233 := by rw [primeFibAux_step_last 388 89 144 233 rfl isPrimeNat_val_233]

theorem primeFib_seven : primeFib 7 = 1597 := by
  calc primeFib 7 = primeFibAux 450 0 1 7 := by rfl
    _ = primeFibAux 449 1 1 7 := by rw [primeFibAux_step_notprime 449 0 1 7 1 rfl isPrimeNat_val_1 (by omega)]
    _ = primeFibAux 448 1 2 6 := by rw [primeFibAux_step_prime 448 1 1 7 2 rfl isPrimeNat_val_2 (by omega)]
    _ = primeFibAux 447 2 3 5 := by rw [primeFibAux_step_prime 447 1 2 6 3 rfl isPrimeNat_val_3 (by omega)]
    _ = primeFibAux 446 3 5 4 := by rw [primeFibAux_step_prime 446 2 3 5 5 rfl isPrimeNat_val_5 (by omega)]
    _ = primeFibAux 445 5 8 4 := by rw [primeFibAux_step_notprime 445 3 5 4 8 rfl isPrimeNat_val_8 (by omega)]
    _ = primeFibAux 444 8 13 3 := by rw [primeFibAux_step_prime 444 5 8 4 13 rfl isPrimeNat_val_13 (by omega)]
    _ = primeFibAux 443 13 21 3 := by rw [primeFibAux_step_notprime 443 8 13 3 21 rfl isPrimeNat_val_21 (by omega)]
    _ = primeFibAux 442 21 34 3 := by rw [primeFibAux_step_notprime 442 13 21 3 34 rfl isPrimeNat_val_34 (by omega)]
    _ = primeFibAux 441 34 55 3 := by rw [primeFibAux_step_notprime 441 21 34 3 55 rfl isPrimeNat_val_55 (by omega)]
    _ = primeFibAux 440 55 89 2 := by rw [primeFibAux_step_prime 440 34 55 3 89 rfl isPrimeNat_val_89 (by omega)]
    _ = primeFibAux 439 89 144 2 := by rw [primeFibAux_step_notprime 439 55 89 2 144 rfl isPrimeNat_val_144 (by omega)]
    _ = primeFibAux 438 144 233 1 := by rw [primeFibAux_step_prime 438 89 144 2 233 rfl isPrimeNat_val_233 (by omega)]
    _ = primeFibAux 437 233 377 1 := by rw [primeFibAux_step_notprime 437 144 233 1 377 rfl isPrimeNat_val_377 (by omega)]
    _ = primeFibAux 436 377 610 1 := by rw [primeFibAux_step_notprime 436 233 377 1 610 rfl isPrimeNat_val_610 (by omega)]
    _ = primeFibAux 435 610 987 1 := by rw [primeFibAux_step_notprime 435 377 610 1 987 rfl isPrimeNat_val_987 (by omega)]
    _ = 1597 := by rw [primeFibAux_step_last 434 610 987 1597 rfl isPrimeNat_val_1597]

theorem primeFib_eight : primeFib 8 = 28657 := by
  calc primeFib 8 = primeFibAux 500 0 1 8 := by rfl
    _ = primeFibAux 499 1 1 8 := by rw [primeFibAux_step_notprime 499 0 1 8 1 rfl isPrimeNat_val_1 (by omega)]
    _ = primeFibAux 498 1 2 7 := by rw [primeFibAux_step_prime 498 1 1 8 2 rfl isPrimeNat_val_2 (by omega)]
    _ = primeFibAux 497 2 3 6 := by rw [primeFibAux_step_prime 497 1 2 7 3 rfl isPrimeNat_val_3 (by omega)]
    _ = primeFibAux 496 3 5 5 := by rw [primeFibAux_step_prime 496 2 3 6 5 rfl isPrimeNat_val_5 (by omega)]
    _ = primeFibAux 495 5 8 5 := by rw [primeFibAux_step_notprime 495 3 5 5 8 rfl isPrimeNat_val_8 (by omega)]
    _ = primeFibAux 494 8 13 4 := by rw [primeFibAux_step_prime 494 5 8 5 13 rfl isPrimeNat_val_13 (by omega)]
    _ = primeFibAux 493 13 21 4 := by rw [primeFibAux_step_notprime 493 8 13 4 21 rfl isPrimeNat_val_21 (by omega)]
    _ = primeFibAux 492 21 34 4 := by rw [primeFibAux_step_notprime 492 13 21 4 34 rfl isPrimeNat_val_34 (by omega)]
    _ = primeFibAux 491 34 55 4 := by rw [primeFibAux_step_notprime 491 21 34 4 55 rfl isPrimeNat_val_55 (by omega)]
    _ = primeFibAux 490 55 89 3 := by rw [primeFibAux_step_prime 490 34 55 4 89 rfl isPrimeNat_val_89 (by omega)]
    _ = primeFibAux 489 89 144 3 := by rw [primeFibAux_step_notprime 489 55 89 3 144 rfl isPrimeNat_val_144 (by omega)]
    _ = primeFibAux 488 144 233 2 := by rw [primeFibAux_step_prime 488 89 144 3 233 rfl isPrimeNat_val_233 (by omega)]
    _ = primeFibAux 487 233 377 2 := by rw [primeFibAux_step_notprime 487 144 233 2 377 rfl isPrimeNat_val_377 (by omega)]
    _ = primeFibAux 486 377 610 2 := by rw [primeFibAux_step_notprime 486 233 377 2 610 rfl isPrimeNat_val_610 (by omega)]
    _ = primeFibAux 485 610 987 2 := by rw [primeFibAux_step_notprime 485 377 610 2 987 rfl isPrimeNat_val_987 (by omega)]
    _ = primeFibAux 484 987 1597 1 := by rw [primeFibAux_step_prime 484 610 987 2 1597 rfl isPrimeNat_val_1597 (by omega)]
    _ = primeFibAux 483 1597 2584 1 := by rw [primeFibAux_step_notprime 483 987 1597 1 2584 rfl isPrimeNat_val_2584 (by omega)]
    _ = primeFibAux 482 2584 4181 1 := by rw [primeFibAux_step_notprime 482 1597 2584 1 4181 rfl isPrimeNat_val_4181 (by omega)]
    _ = primeFibAux 481 4181 6765 1 := by rw [primeFibAux_step_notprime 481 2584 4181 1 6765 rfl isPrimeNat_val_6765 (by omega)]
    _ = primeFibAux 480 6765 10946 1 := by rw [primeFibAux_step_notprime 480 4181 6765 1 10946 rfl isPrimeNat_val_10946 (by omega)]
    _ = primeFibAux 479 10946 17711 1 := by rw [primeFibAux_step_notprime 479 6765 10946 1 17711 rfl isPrimeNat_val_17711 (by omega)]
    _ = 28657 := by rw [primeFibAux_step_last 478 10946 17711 28657 rfl isPrimeNat_val_28657]

theorem primeFib_nine : primeFib 9 = 514229 := by
  calc primeFib 9 = primeFibAux 550 0 1 9 := by rfl
    _ = primeFibAux 549 1 1 9 := by rw [primeFibAux_step_notprime 549 0 1 9 1 rfl isPrimeNat_val_1 (by omega)]
    _ = primeFibAux 548 1 2 8 := by rw [primeFibAux_step_prime 548 1 1 9 2 rfl isPrimeNat_val_2 (by omega)]
    _ = primeFibAux 547 2 3 7 := by rw [primeFibAux_step_prime 547 1 2 8 3 rfl isPrimeNat_val_3 (by omega)]
    _ = primeFibAux 546 3 5 6 := by rw [primeFibAux_step_prime 546 2 3 7 5 rfl isPrimeNat_val_5 (by omega)]
    _ = primeFibAux 545 5 8 6 := by rw [primeFibAux_step_notprime 545 3 5 6 8 rfl isPrimeNat_val_8 (by omega)]
    _ = primeFibAux 544 8 13 5 := by rw [primeFibAux_step_prime 544 5 8 6 13 rfl isPrimeNat_val_13 (by omega)]
    _ = primeFibAux 543 13 21 5 := by rw [primeFibAux_step_notprime 543 8 13 5 21 rfl isPrimeNat_val_21 (by omega)]
    _ = primeFibAux 542 21 34 5 := by rw [primeFibAux_step_notprime 542 13 21 5 34 rfl isPrimeNat_val_34 (by omega)]
    _ = primeFibAux 541 34 55 5 := by rw [primeFibAux_step_notprime 541 21 34 5 55 rfl isPrimeNat_val_55 (by omega)]
    _ = primeFibAux 540 55 89 4 := by rw [primeFibAux_step_prime 540 34 55 5 89 rfl isPrimeNat_val_89 (by omega)]
    _ = primeFibAux 539 89 144 4 := by rw [primeFibAux_step_notprime 539 55 89 4 144 rfl isPrimeNat_val_144 (by omega)]
    _ = primeFibAux 538 144 233 3 := by rw [primeFibAux_step_prime 538 89 144 4 233 rfl isPrimeNat_val_233 (by omega)]
    _ = primeFibAux 537 233 377 3 := by rw [primeFibAux_step_notprime 537 144 233 3 377 rfl isPrimeNat_val_377 (by omega)]
    _ = primeFibAux 536 377 610 3 := by rw [primeFibAux_step_notprime 536 233 377 3 610 rfl isPrimeNat_val_610 (by omega)]
    _ = primeFibAux 535 610 987 3 := by rw [primeFibAux_step_notprime 535 377 610 3 987 rfl isPrimeNat_val_987 (by omega)]
    _ = primeFibAux 534 987 1597 2 := by rw [primeFibAux_step_prime 534 610 987 3 1597 rfl isPrimeNat_val_1597 (by omega)]
    _ = primeFibAux 533 1597 2584 2 := by rw [primeFibAux_step_notprime 533 987 1597 2 2584 rfl isPrimeNat_val_2584 (by omega)]
    _ = primeFibAux 532 2584 4181 2 := by rw [primeFibAux_step_notprime 532 1597 2584 2 4181 rfl isPrimeNat_val_4181 (by omega)]
    _ = primeFibAux 531 4181 6765 2 := by rw [primeFibAux_step_notprime 531 2584 4181 2 6765 rfl isPrimeNat_val_6765 (by omega)]
    _ = primeFibAux 530 6765 10946 2 := by rw [primeFibAux_step_notprime 530 4181 6765 2 10946 rfl isPrimeNat_val_10946 (by omega)]
    _ = primeFibAux 529 10946 17711 2 := by rw [primeFibAux_step_notprime 529 6765 10946 2 17711 rfl isPrimeNat_val_17711 (by omega)]
    _ = primeFibAux 528 17711 28657 1 := by rw [primeFibAux_step_prime 528 10946 17711 2 28657 rfl isPrimeNat_val_28657 (by omega)]
    _ = primeFibAux 527 28657 46368 1 := by rw [primeFibAux_step_notprime 527 17711 28657 1 46368 rfl isPrimeNat_val_46368 (by omega)]
    _ = primeFibAux 526 46368 75025 1 := by rw [primeFibAux_step_notprime 526 28657 46368 1 75025 rfl isPrimeNat_val_75025 (by omega)]
    _ = primeFibAux 525 75025 121393 1 := by rw [primeFibAux_step_notprime 525 46368 75025 1 121393 rfl isPrimeNat_val_121393 (by omega)]
    _ = primeFibAux 524 121393 196418 1 := by rw [primeFibAux_step_notprime 524 75025 121393 1 196418 rfl isPrimeNat_val_196418 (by omega)]
    _ = primeFibAux 523 196418 317811 1 := by rw [primeFibAux_step_notprime 523 121393 196418 1 317811 rfl isPrimeNat_val_317811 (by omega)]
    _ = 514229 := by rw [primeFibAux_step_last 522 196418 317811 514229 rfl isPrimeNat_val_514229]

theorem primeFib_ten : primeFib 10 = 433494437 := by
  calc primeFib 10 = primeFibAux 600 0 1 10 := by rfl
    _ = primeFibAux 599 1 1 10 := by rw [primeFibAux_step_notprime 599 0 1 10 1 rfl isPrimeNat_val_1 (by omega)]
    _ = primeFibAux 598 1 2 9 := by rw [primeFibAux_step_prime 598 1 1 10 2 rfl isPrimeNat_val_2 (by omega)]
    _ = primeFibAux 597 2 3 8 := by rw [primeFibAux_step_prime 597 1 2 9 3 rfl isPrimeNat_val_3 (by omega)]
    _ = primeFibAux 596 3 5 7 := by rw [primeFibAux_step_prime 596 2 3 8 5 rfl isPrimeNat_val_5 (by omega)]
    _ = primeFibAux 595 5 8 7 := by rw [primeFibAux_step_notprime 595 3 5 7 8 rfl isPrimeNat_val_8 (by omega)]
    _ = primeFibAux 594 8 13 6 := by rw [primeFibAux_step_prime 594 5 8 7 13 rfl isPrimeNat_val_13 (by omega)]
    _ = primeFibAux 593 13 21 6 := by rw [primeFibAux_step_notprime 593 8 13 6 21 rfl isPrimeNat_val_21 (by omega)]
    _ = primeFibAux 592 21 34 6 := by rw [primeFibAux_step_notprime 592 13 21 6 34 rfl isPrimeNat_val_34 (by omega)]
    _ = primeFibAux 591 34 55 6 := by rw [primeFibAux_step_notprime 591 21 34 6 55 rfl isPrimeNat_val_55 (by omega)]
    _ = primeFibAux 590 55 89 5 := by rw [primeFibAux_step_prime 590 34 55 6 89 rfl isPrimeNat_val_89 (by omega)]
    _ = primeFibAux 589 89 144 5 := by rw [primeFibAux_step_notprime 589 55 89 5 144 rfl isPrimeNat_val_144 (by omega)]
    _ = primeFibAux 588 144 233 4 := by rw [primeFibAux_step_prime 588 89 144 5 233 rfl isPrimeNat_val_233 (by omega)]
    _ = primeFibAux 587 233 377 4 := by rw [primeFibAux_step_notprime 587 144 233 4 377 rfl isPrimeNat_val_377 (by omega)]
    _ = primeFibAux 586 377 610 4 := by rw [primeFibAux_step_notprime 586 233 377 4 610 rfl isPrimeNat_val_610 (by omega)]
    _ = primeFibAux 585 610 987 4 := by rw [primeFibAux_step_notprime 585 377 610 4 987 rfl isPrimeNat_val_987 (by omega)]
    _ = primeFibAux 584 987 1597 3 := by rw [primeFibAux_step_prime 584 610 987 4 1597 rfl isPrimeNat_val_1597 (by omega)]
    _ = primeFibAux 583 1597 2584 3 := by rw [primeFibAux_step_notprime 583 987 1597 3 2584 rfl isPrimeNat_val_2584 (by omega)]
    _ = primeFibAux 582 2584 4181 3 := by rw [primeFibAux_step_notprime 582 1597 2584 3 4181 rfl isPrimeNat_val_4181 (by omega)]
    _ = primeFibAux 581 4181 6765 3 := by rw [primeFibAux_step_notprime 581 2584 4181 3 6765 rfl isPrimeNat_val_6765 (by omega)]
    _ = primeFibAux 580 6765 10946 3 := by rw [primeFibAux_step_notprime 580 4181 6765 3 10946 rfl isPrimeNat_val_10946 (by omega)]
    _ = primeFibAux 579 10946 17711 3 := by rw [primeFibAux_step_notprime 579 6765 10946 3 17711 rfl isPrimeNat_val_17711 (by omega)]
    _ = primeFibAux 578 17711 28657 2 := by rw [primeFibAux_step_prime 578 10946 17711 3 28657 rfl isPrimeNat_val_28657 (by omega)]
    _ = primeFibAux 577 28657 46368 2 := by rw [primeFibAux_step_notprime 577 17711 28657 2 46368 rfl isPrimeNat_val_46368 (by omega)]
    _ = primeFibAux 576 46368 75025 2 := by rw [primeFibAux_step_notprime 576 28657 46368 2 75025 rfl isPrimeNat_val_75025 (by omega)]
    _ = primeFibAux 575 75025 121393 2 := by rw [primeFibAux_step_notprime 575 46368 75025 2 121393 rfl isPrimeNat_val_121393 (by omega)]
    _ = primeFibAux 574 121393 196418 2 := by rw [primeFibAux_step_notprime 574 75025 121393 2 196418 rfl isPrimeNat_val_196418 (by omega)]
    _ = primeFibAux 573 196418 317811 2 := by rw [primeFibAux_step_notprime 573 121393 196418 2 317811 rfl isPrimeNat_val_317811 (by omega)]
    _ = primeFibAux 572 317811 514229 1 := by rw [primeFibAux_step_prime 572 196418 317811 2 514229 rfl isPrimeNat_val_514229 (by omega)]
    _ = primeFibAux 571 514229 832040 1 := by rw [primeFibAux_step_notprime 571 317811 514229 1 832040 rfl isPrimeNat_val_832040 (by omega)]
    _ = primeFibAux 570 832040 1346269 1 := by rw [primeFibAux_step_notprime 570 514229 832040 1 1346269 rfl isPrimeNat_val_1346269 (by omega)]
    _ = primeFibAux 569 1346269 2178309 1 := by rw [primeFibAux_step_notprime 569 832040 1346269 1 2178309 rfl isPrimeNat_val_2178309 (by omega)]
    _ = primeFibAux 568 2178309 3524578 1 := by rw [primeFibAux_step_notprime 568 1346269 2178309 1 3524578 rfl isPrimeNat_val_3524578 (by omega)]
    _ = primeFibAux 567 3524578 5702887 1 := by rw [primeFibAux_step_notprime 567 2178309 3524578 1 5702887 rfl isPrimeNat_val_5702887 (by omega)]
    _ = primeFibAux 566 5702887 9227465 1 := by rw [primeFibAux_step_notprime 566 3524578 5702887 1 9227465 rfl isPrimeNat_val_9227465 (by omega)]
    _ = primeFibAux 565 9227465 14930352 1 := by rw [primeFibAux_step_notprime 565 5702887 9227465 1 14930352 rfl isPrimeNat_val_14930352 (by omega)]
    _ = primeFibAux 564 14930352 24157817 1 := by rw [primeFibAux_step_notprime 564 9227465 14930352 1 24157817 rfl isPrimeNat_val_24157817 (by omega)]
    _ = primeFibAux 563 24157817 39088169 1 := by rw [primeFibAux_step_notprime 563 14930352 24157817 1 39088169 rfl isPrimeNat_val_39088169 (by omega)]
    _ = primeFibAux 562 39088169 63245986 1 := by rw [primeFibAux_step_notprime 562 24157817 39088169 1 63245986 rfl isPrimeNat_val_63245986 (by omega)]
    _ = primeFibAux 561 63245986 102334155 1 := by rw [primeFibAux_step_notprime 561 39088169 63245986 1 102334155 rfl isPrimeNat_val_102334155 (by omega)]
    _ = primeFibAux 560 102334155 165580141 1 := by rw [primeFibAux_step_notprime 560 63245986 102334155 1 165580141 rfl isPrimeNat_val_165580141 (by omega)]
    _ = primeFibAux 559 165580141 267914296 1 := by rw [primeFibAux_step_notprime 559 102334155 165580141 1 267914296 rfl isPrimeNat_val_267914296 (by omega)]
    _ = 433494437 := by rw [primeFibAux_step_last 558 165580141 267914296 433494437 rfl isPrimeNat_val_433494437]


/-!
## 3. Precondition
-/

/-- Precondition of `prime_fib(n)`: `n` is a 1-based index (`0 < n`) and the search does find the
`n`-th prime Fibonacci number inside its horizon (`primeFib n ≠ 0`).

The second conjunct is not an artificial strengthening.  The Python loop is `while True` with no
horizon, and it terminates for a given `n` exactly when at least `n` prime Fibonacci numbers
exist; that this happens for every `n` is the open problem "are there infinitely many prime
Fibonacci numbers?", so no proof of it can exist.  We therefore record successful termination as
an assumption.  For every `n` for which the `n`-th prime Fibonacci number is known (in particular
for all `n ≤ 26`, the largest known one being `Nat.fib 569`) the horizon `fuelOf n = 50 * (n + 2)`
is far above the required index, so `Pre n` holds there — as witnessed by `primeFib_one` …
`primeFib_ten` above. -/
def Pre (n : Nat) : Prop := 0 < n ∧ primeFib n ≠ 0

/-!
## 4. Properties
-/

/-- `v` is the `n`-th prime Fibonacci number: `v = Nat.fib m` for an index `m` at which the
running count of prime Fibonacci numbers reaches `n`, and `v` itself is prime. -/
def NthPrimeFib (n v : Nat) : Prop :=
  ∃ m, Nat.fib m = v ∧ countPrimeFib m = n ∧ Nat.Prime v

/-- Property 1 (`is_prime(f[-1])` held when the loop returned): the result is prime. -/
def prime_fib_prime_prop (_n v : Nat) : Prop := Nat.Prime v

/-- Property 2 (`v` was appended to the Fibonacci list `f`): the result is a Fibonacci number. -/
def prime_fib_fib_prop (_n v : Nat) : Prop := ∃ m, Nat.fib m = v

/-- Property 3 (the counter `n` was decremented exactly once per prime Fibonacci number): among
`fib 0, …, fib m` with `fib m = v` exactly `n` are prime, i.e. `v` is the `n`-th one. -/
def prime_fib_count_prop (n v : Nat) : Prop := ∃ m, Nat.fib m = v ∧ countPrimeFib m = n

/-- Property 4: the `n`-th prime Fibonacci number is uniquely determined by property 3. -/
def prime_fib_unique_prop (n v : Nat) : Prop := ∀ w, NthPrimeFib n w → w = v

/-- Property 5: consecutive answers strictly increase (the loop scans the Fibonacci sequence in
increasing order and returns as soon as the counter hits `0`). -/
def prime_fib_increasing_prop (n v w : Nat) : Prop :=
  NthPrimeFib n v → NthPrimeFib (n + 1) w → v < w

/-- The main soundness lemma: whenever the loop stops with a nonzero answer, that answer is a
prime Fibonacci number and the running count `countPrimeFib` has increased by exactly `n`.

The state is described by `a = Nat.fib j`, `b = Nat.fib (j + 1)` (the last two entries of the
Python list `f`, which is `[fib 0, …, fib (j + 1)]`) and `c = countPrimeFib (j + 1)` (how often
the counter has already been decremented). -/
theorem primeFibAux_sound : ∀ (fuel a b n j c : Nat),
    a = Nat.fib j → b = Nat.fib (j + 1) → countPrimeFib (j + 1) = c → 0 < n →
    primeFibAux fuel a b n ≠ 0 →
    ∃ m, Nat.fib m = primeFibAux fuel a b n ∧ countPrimeFib m = c + n ∧
      Nat.Prime (primeFibAux fuel a b n) := by
  intro fuel
  induction fuel with
  | zero =>
      intro a b n j c ha hb hc hn h
      exact absurd rfl h
  | succ fuel ih =>
      intro a b n j c ha hb hc hn h
      have hsum : a + b = Nat.fib (j + 2) := by
        rw [ha, hb]
        exact (Nat.fib_add_two (n := j)).symm
      by_cases hp : isPrimeNat (a + b) = true
      · have hprime : Nat.Prime (Nat.fib (j + 2)) := by
          rw [← hsum]
          exact isPrimeNat_true_iff.mp hp
        have hcnt : countPrimeFib (j + 1 + 1) = c + 1 := by
          rw [countPrimeFib_succ (j + 1), hc, if_pos hprime]
        by_cases hz : n - 1 = 0
        · have hn1 : n = 1 := by omega
          have hres : primeFibAux (fuel + 1) a b n = a + b := by
            rw [hn1]
            exact primeFibAux_step_last fuel a b (a + b) rfl hp
          refine ⟨j + 2, ?_, ?_, ?_⟩
          · rw [hres]; exact hsum.symm
          · rw [hn1]; exact hcnt
          · rw [hres, hsum]; exact hprime
        · have hn' : 0 < n - 1 := Nat.pos_of_ne_zero hz
          have hres : primeFibAux (fuel + 1) a b n = primeFibAux fuel b (a + b) (n - 1) :=
            primeFibAux_step_prime fuel a b n (a + b) rfl hp (by omega)
          have hne : primeFibAux fuel b (a + b) (n - 1) ≠ 0 := by rwa [← hres]
          obtain ⟨m, hm1, hm2, hm3⟩ :=
            ih b (a + b) (n - 1) (j + 1) (c + 1) hb hsum hcnt hn' hne
          refine ⟨m, ?_, ?_, ?_⟩
          · rw [hres]; exact hm1
          · have h1 : 1 ≤ n := hn
            omega
          · rw [hres]; exact hm3
      · have hnp : isPrimeNat (a + b) = false := by
          cases hb' : isPrimeNat (a + b) <;> simp_all
        have hnprime : ¬ Nat.Prime (Nat.fib (j + 2)) := by
          rw [← hsum]
          exact isPrimeNat_false_iff.mp hnp
        have hcnt : countPrimeFib (j + 1 + 1) = c + 0 := by
          rw [countPrimeFib_succ (j + 1), hc, if_neg hnprime]
        by_cases hz : n = 0
        · exact absurd hn (by omega)
        · have hres : primeFibAux (fuel + 1) a b n = primeFibAux fuel b (a + b) n :=
            primeFibAux_step_notprime fuel a b n (a + b) rfl hnp (by omega)
          have hne : primeFibAux fuel b (a + b) n ≠ 0 := by rwa [← hres]
          obtain ⟨m, hm1, hm2, hm3⟩ :=
            ih b (a + b) n (j + 1) (c + 0) hb hsum hcnt hn hne
          refine ⟨m, ?_, ?_, ?_⟩
          · rw [hres]; exact hm1
          · omega
          · rw [hres]; exact hm3

/-- Soundness for the top-level function: `primeFib n` really is the `n`-th prime Fibonacci
number. -/
theorem primeFib_sound (n : Nat) (hn : 0 < n) (h : primeFib n ≠ 0) :
    NthPrimeFib n (primeFib n) := by
  have h0 : (0 : Nat) = Nat.fib 0 := by simp
  have h1 : (1 : Nat) = Nat.fib (0 + 1) := by simp
  have hc : countPrimeFib (0 + 1) = 0 := by simp
  obtain ⟨m, hm1, hm2, hm3⟩ :=
    primeFibAux_sound (fuelOf n) 0 1 n 0 0 h0 h1 hc hn h
  exact ⟨m, hm1, by simpa using hm2, hm3⟩

/-- Two numbers that both satisfy the "`n`-th prime Fibonacci number" specification are equal. -/
theorem NthPrimeFib_unique {n v w : Nat} (hv : NthPrimeFib n v) (hw : NthPrimeFib n w) :
    v = w := by
  obtain ⟨mv, hfv, hcv, hpv⟩ := hv
  obtain ⟨mw, hfw, hcw, hpw⟩ := hw
  have hmv0 : 0 < mv := by
    by_contra h0
    have hm : mv = 0 := by omega
    rw [hm, Nat.fib_zero] at hfv
    have h0 : Nat.Prime 0 := by rw [hfv]; exact hpv
    exact Nat.not_prime_zero h0
  have hmw0 : 0 < mw := by
    by_contra h0
    have hm : mw = 0 := by omega
    rw [hm, Nat.fib_zero] at hfw
    have h0 : Nat.Prime 0 := by rw [hfw]; exact hpw
    exact Nat.not_prime_zero h0
  have hfv' : Nat.Prime (Nat.fib mv) := by rw [hfv]; exact hpv
  have hfw' : Nat.Prime (Nat.fib mw) := by rw [hfw]; exact hpw
  have hev : countPrimeFib mv = countPrimeFib mw := by rw [hcv, hcw]
  by_cases hlt : mv < mw
  · have h1 := countPrimeFib_succ_prime hmw0 hfw'
    have h2 : countPrimeFib mv ≤ countPrimeFib (mw - 1) := countPrimeFib_mono (by omega)
    omega
  · by_cases hgt : mw < mv
    · have h1 := countPrimeFib_succ_prime hmv0 hfv'
      have h2 : countPrimeFib mw ≤ countPrimeFib (mv - 1) := countPrimeFib_mono (by omega)
      omega
    · have hmvw : mv = mw := by omega
      rw [← hfv, ← hfw, hmvw]

theorem prime_fib_prime_thm (n : Nat) (h : Pre n) : prime_fib_prime_prop n (primeFib n) := by
  obtain ⟨m, hm1, hm2, hm3⟩ := primeFib_sound n h.1 h.2
  exact hm3

theorem prime_fib_fib_thm (n : Nat) (h : Pre n) : prime_fib_fib_prop n (primeFib n) := by
  obtain ⟨m, hm1, hm2, hm3⟩ := primeFib_sound n h.1 h.2
  exact ⟨m, hm1⟩

theorem prime_fib_count_thm (n : Nat) (h : Pre n) : prime_fib_count_prop n (primeFib n) := by
  obtain ⟨m, hm1, hm2, hm3⟩ := primeFib_sound n h.1 h.2
  exact ⟨m, hm1, hm2⟩

theorem prime_fib_unique_thm (n : Nat) (h : Pre n) : prime_fib_unique_prop n (primeFib n) := by
  obtain ⟨m, hm1, hm2, hm3⟩ := primeFib_sound n h.1 h.2
  intro w hw
  exact NthPrimeFib_unique hw ⟨m, hm1, hm2, hm3⟩

theorem prime_fib_increasing_prop_thm (n v w : Nat) :
    prime_fib_increasing_prop n v w := by
  intro hv hw
  obtain ⟨mv, hfv, hcv, hpv⟩ := hv
  obtain ⟨mw, hfw, hcw, hpw⟩ := hw
  have hlt : mv < mw := by
    by_contra h
    push_neg at h
    have := countPrimeFib_mono h
    omega
  have h2 : 2 ≤ mv := by
    by_contra h
    push_neg at h
    have hf : Nat.fib mv ≤ 1 := by
      have hle : mv ≤ 2 := by omega
      interval_cases mv <;> simp [Nat.fib_zero, Nat.fib_one]
    rw [← hfv] at hpv
    exact Nat.not_le_of_lt (Nat.Prime.one_lt hpv) hf
  rw [← hfv, ← hfw]
  exact (Nat.fib_lt_fib h2).mpr hlt

/-- Consecutive answers of the program strictly increase. -/
theorem prime_fib_increasing_thm (n : Nat) (hn : Pre n) (hn1 : Pre (n + 1)) :
    primeFib n < primeFib (n + 1) :=
  prime_fib_increasing_prop_thm n (primeFib n) (primeFib (n + 1))
    (primeFib_sound n hn.1 hn.2) (primeFib_sound (n + 1) hn1.1 hn1.2)

/-!
## 5. Postcondition
-/

/-- Postcondition of `prime_fib(n)`: the returned value is prime, is a Fibonacci number, is the
`n`-th number with both of those properties, and is the only such number. -/
def Post_prop (n v : Nat) : Prop :=
  prime_fib_prime_prop n v ∧ prime_fib_fib_prop n v ∧ prime_fib_count_prop n v ∧
    prime_fib_unique_prop n v

/-!
## 6. Property-based tests

Every property above has an executable Boolean counterpart, tested here exhaustively on small
inputs (bounded PBTs, `native_decide`) and on random inputs (Plausible).  `45` is a safe index
bound: the answers `primeFib 1 … primeFib 10` are `Nat.fib 3 … Nat.fib 43`.
-/

/-- Executable Fibonacci-index lookup: the least `m ≤ bound` with `Nat.fib m = v`. -/
def fibIndexOpt (bound v : Nat) : Option Nat :=
  (List.range (bound + 1)).find? (fun m => Nat.fib m == v)

/-- Executable counterpart of `prime_fib_count_prop`. -/
def nthCheck (bound n v : Nat) : Bool :=
  match fibIndexOpt bound v with
  | none => false
  | some m => countPrimeFib m == n

/-- Executable counterpart of `prime_fib_unique_prop`: no index `m ≤ bound` other than one with
`Nat.fib m = v` realises "exactly `n` prime Fibonacci numbers up to `m`, and `Nat.fib m` prime". -/
def uniqueCheck (bound n v : Nat) : Bool :=
  (List.range (bound + 1)).all (fun m =>
    !((countPrimeFib m == n) && decide (Nat.Prime (Nat.fib m))) || (Nat.fib m == v))

/-- Executable counterpart of `Post_prop`. -/
def Post_check (bound n v : Nat) : Bool :=
  decide (Nat.Prime v) && (fibIndexOpt bound v).isSome && nthCheck bound n v &&
    uniqueCheck bound n v

-- PBT (bounded) for `isPrimeNat_true_iff`: the trial-division test agrees with `Nat.Prime`.
example : (List.range 500).all (fun p => isPrimeNat p == decide (Nat.Prime p)) = true := by
  native_decide

-- PBT (bounded): `countPrimeFib` really counts the prime Fibonacci numbers.
example : (List.range 45).all (fun m =>
    countPrimeFib m == ((List.range (m + 1)).filter (fun i => decide (Nat.Prime (Nat.fib i)))).length) =
  true := by native_decide

-- PBT (bounded) for `prime_fib_prime_prop`.
example : (List.range 10).all (fun i => decide (Nat.Prime (primeFib (i + 1)))) = true := by
  native_decide

-- PBT (bounded) for `prime_fib_fib_prop`.
example : (List.range 10).all (fun i => (fibIndexOpt 45 (primeFib (i + 1))).isSome) = true := by
  native_decide

-- PBT (bounded) for `prime_fib_count_prop`.
example : (List.range 10).all (fun i => nthCheck 45 (i + 1) (primeFib (i + 1))) = true := by
  native_decide

-- PBT (bounded) for `prime_fib_unique_prop`.
example : (List.range 10).all (fun i => uniqueCheck 45 (i + 1) (primeFib (i + 1))) = true := by
  native_decide

-- PBT (bounded) for `prime_fib_increasing_prop`.
example : (List.range 9).all (fun i => primeFib (i + 1) < primeFib (i + 2)) = true := by
  native_decide

-- PBT (bounded) for `Post_prop`.
example : (List.range 10).all (fun i => Post_check 45 (i + 1) (primeFib (i + 1))) = true := by
  native_decide

-- Randomized PBT for `prime_fib_prime_prop` (the sampled index is mapped into the admissible
-- range `1 … 10`, so no sample is discarded).
#eval Plausible.Testable.check (∀ k : Nat, decide (Nat.Prime (primeFib (k % 10 + 1))) = true)

-- Randomized PBT for `prime_fib_count_prop`.
#eval Plausible.Testable.check
  (∀ k : Nat, nthCheck 45 (k % 10 + 1) (primeFib (k % 10 + 1)) = true)

-- Randomized PBT for `prime_fib_unique_prop`.
#eval Plausible.Testable.check
  (∀ k : Nat, uniqueCheck 45 (k % 10 + 1) (primeFib (k % 10 + 1)) = true)

-- Randomized PBT for `prime_fib_increasing_prop`.
#eval Plausible.Testable.check (∀ k : Nat, primeFib (k % 9 + 1) < primeFib (k % 9 + 2))

-- Randomized PBT for `Post_prop`.
#eval Plausible.Testable.check
  (∀ k : Nat, Post_check 45 (k % 10 + 1) (primeFib (k % 10 + 1)) = true)

-- Randomized PBT for `isPrimeNat_true_iff`.
#eval Plausible.Testable.check (∀ p : Nat, isPrimeNat (p % 400) = decide (Nat.Prime (p % 400)))

/-!
## 7. Correctness: `Pre → Post`
-/

theorem prime_fib_correct (n : Nat) (h : Pre n) : Post_prop n (primeFib n) :=
  ⟨prime_fib_prime_thm n h, prime_fib_fib_thm n h, prime_fib_count_thm n h,
    prime_fib_unique_thm n h⟩

/-- The answer is at least `2`, since it is a prime. -/
theorem primeFib_ge_two (n : Nat) (h : Pre n) : 2 ≤ primeFib n :=
  Nat.Prime.two_le (prime_fib_prime_thm n h)

/-- The answer is `Nat.fib m` for an index `m ≥ 3` at which the running count reaches `n`
(`Nat.fib 0 = 0`, `Nat.fib 1 = Nat.fib 2 = 1` are not prime). -/
theorem primeFib_index (n : Nat) (h : Pre n) :
    ∃ m, 3 ≤ m ∧ Nat.fib m = primeFib n ∧ countPrimeFib m = n := by
  obtain ⟨m, hm1, hm2, hm3⟩ := primeFib_sound n h.1 h.2
  refine ⟨m, ?_, hm1, hm2⟩
  by_contra hm
  push_neg at hm
  have hf : Nat.fib m ≤ 1 := by
    have hle : m ≤ 2 := by omega
    interval_cases m <;> simp [Nat.fib_zero, Nat.fib_one]
  rw [← hm1] at hm3
  exact Nat.not_le_of_lt (Nat.Prime.one_lt hm3) hf

/-- If the program terminates with an answer, the `n`-th prime Fibonacci number exists. -/
theorem Pre_imp_exists (n : Nat) (h : Pre n) :
    ∃ m, countPrimeFib m = n ∧ Nat.Prime (Nat.fib m) := by
  obtain ⟨m, hm, hm1, hm2⟩ := primeFib_index n h
  exact ⟨m, hm2, by rw [hm1]; exact prime_fib_prime_thm n h⟩

/-!
### The precondition is satisfiable and the postcondition holds on the Python test suite
-/


theorem Pre_one : Pre 1 := ⟨by omega, by rw [primeFib_one]; omega⟩
theorem Pre_two : Pre 2 := ⟨by omega, by rw [primeFib_two]; omega⟩
theorem Pre_three : Pre 3 := ⟨by omega, by rw [primeFib_three]; omega⟩
theorem Pre_four : Pre 4 := ⟨by omega, by rw [primeFib_four]; omega⟩
theorem Pre_five : Pre 5 := ⟨by omega, by rw [primeFib_five]; omega⟩
theorem Pre_six : Pre 6 := ⟨by omega, by rw [primeFib_six]; omega⟩
theorem Pre_seven : Pre 7 := ⟨by omega, by rw [primeFib_seven]; omega⟩
theorem Pre_eight : Pre 8 := ⟨by omega, by rw [primeFib_eight]; omega⟩
theorem Pre_nine : Pre 9 := ⟨by omega, by rw [primeFib_nine]; omega⟩
theorem Pre_ten : Pre 10 := ⟨by omega, by rw [primeFib_ten]; omega⟩

theorem Post_one : Post_prop 1 2 := by
  have h : primeFib 1 = 2 := primeFib_one
  rw [← h]
  exact prime_fib_correct 1 Pre_one

theorem Post_two : Post_prop 2 3 := by
  have h : primeFib 2 = 3 := primeFib_two
  rw [← h]
  exact prime_fib_correct 2 Pre_two

theorem Post_three : Post_prop 3 5 := by
  have h : primeFib 3 = 5 := primeFib_three
  rw [← h]
  exact prime_fib_correct 3 Pre_three

theorem Post_four : Post_prop 4 13 := by
  have h : primeFib 4 = 13 := primeFib_four
  rw [← h]
  exact prime_fib_correct 4 Pre_four

theorem Post_five : Post_prop 5 89 := by
  have h : primeFib 5 = 89 := primeFib_five
  rw [← h]
  exact prime_fib_correct 5 Pre_five

theorem Post_six : Post_prop 6 233 := by
  have h : primeFib 6 = 233 := primeFib_six
  rw [← h]
  exact prime_fib_correct 6 Pre_six

theorem Post_seven : Post_prop 7 1597 := by
  have h : primeFib 7 = 1597 := primeFib_seven
  rw [← h]
  exact prime_fib_correct 7 Pre_seven

theorem Post_eight : Post_prop 8 28657 := by
  have h : primeFib 8 = 28657 := primeFib_eight
  rw [← h]
  exact prime_fib_correct 8 Pre_eight

theorem Post_nine : Post_prop 9 514229 := by
  have h : primeFib 9 = 514229 := primeFib_nine
  rw [← h]
  exact prime_fib_correct 9 Pre_nine

theorem Post_ten : Post_prop 10 433494437 := by
  have h : primeFib 10 = 433494437 := primeFib_ten
  rw [← h]
  exact prime_fib_correct 10 Pre_ten

/-!
## 8. Imperative implementation

Mutable state in a `do` block, mirroring the Python loop.  The list `f` of the reference program is
only ever read through `f[-1]` and `f[-2]`, so the two registers `prev` and `curr` hold exactly the
information the loop uses.
-/

/-- Mutable state of the Python loop: `prev` and `curr` are `f[-2]` and `f[-1]`, `remaining` is the
counter `n`, `result` is the value to return and `done` records that the `return` was taken. -/
structure ImpState where
  prev : Nat
  curr : Nat
  remaining : Nat
  result : Nat
  done : Bool

/-- One execution of the Python loop body: append `prev + curr` to `f`, decrement the counter when
the appended value is prime, and return as soon as the counter reaches `0`. -/
def impStep (s : ImpState) : ImpState :=
  if s.done then s
  else
    let v := s.prev + s.curr
    let r := if isPrimeNat v then s.remaining - 1 else s.remaining
    if r = 0 then
      { prev := s.curr, curr := v, remaining := r, result := v, done := true }
    else
      { prev := s.curr, curr := v, remaining := r, result := s.result, done := false }

/-- `fuel` executions of the loop body. -/
def impIter : Nat → ImpState → ImpState
  | 0, s => s
  | fuel + 1, s => impIter fuel (impStep s)

theorem impIter_done (fuel : Nat) {s : ImpState} (h : s.done = true) : impIter fuel s = s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ f ih => simp [impIter, impStep, h, ih]

theorem impStep_terminate (s : ImpState) (hd : s.done = false)
    (hz : (if isPrimeNat (s.prev + s.curr) = true then s.remaining - 1 else s.remaining) = 0) :
    impStep s = { prev := s.curr, curr := s.prev + s.curr, remaining := 0,
                  result := s.prev + s.curr, done := true } := by
  simp [impStep, hd, hz]

theorem impStep_continue (s : ImpState) (hd : s.done = false)
    (hz : ¬((if isPrimeNat (s.prev + s.curr) = true then s.remaining - 1 else s.remaining) = 0)) :
    impStep s = { prev := s.curr, curr := s.prev + s.curr,
                  remaining := (if isPrimeNat (s.prev + s.curr) = true
                                then s.remaining - 1 else s.remaining),
                  result := s.result, done := false } := by
  simp [impStep, hd, hz]

/-- The imperative implementation of `prime_fib`: `Id.run do` with mutable state. -/
def primeFibImp (n : Nat) : Nat :=
  (Id.run do
    let mut s : ImpState := { prev := 0, curr := 1, remaining := n, result := 0, done := false }
    for _ in List.range (fuelOf n) do
      s := impStep s
    return s).result

theorem impLoop_forM : ∀ (l : List Nat) (s : ImpState),
    (Id.run do
      let mut t := s
      for _ in l do t := impStep t
      return t) = impIter l.length s := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons x xs ih =>
      intro s
      have hstep : (Id.run do
          let mut t := s
          for _ in (x :: xs) do t := impStep t
          return t) =
        (Id.run do
          let mut t := impStep s
          for _ in xs do t := impStep t
          return t) := by simp
      rw [hstep, ih, List.length_cons]
      rfl

theorem impLoop_range (fuel : Nat) (s : ImpState) :
    (Id.run do
      let mut t := s
      for _ in List.range fuel do t := impStep t
      return t) = impIter fuel s := by
  have h := impLoop_forM (List.range fuel) s
  rw [List.length_range] at h
  exact h

theorem primeFibImp_iter (n fuel : Nat) :
    (Id.run do
      let mut s : ImpState := { prev := 0, curr := 1, remaining := n, result := 0, done := false }
      for _ in List.range fuel do s := impStep s
      return s) =
    impIter fuel { prev := 0, curr := 1, remaining := n, result := 0, done := false } := by
  exact impLoop_range fuel { prev := 0, curr := 1, remaining := n, result := 0, done := false }

/-- The imperative loop and the functional recursion compute the same answer: the loop invariant
is "`prev = fib j`, `curr = fib (j+1)`, `remaining` prime Fibonacci numbers still to go". -/
theorem impIter_res : ∀ (fuel : Nat) (s : ImpState), s.done = false → s.result = 0 →
    (impIter fuel s).result = primeFibAux fuel s.prev s.curr s.remaining := by
  intro fuel
  induction fuel with
  | zero => intro s _ hr; exact hr
  | succ f ih =>
      intro s hd hr
      have e : impIter (f + 1) s = impIter f (impStep s) := rfl
      rw [e]
      by_cases hz : (if isPrimeNat (s.prev + s.curr) = true then s.remaining - 1 else s.remaining) = 0
      · have h1 := impStep_terminate s hd hz
        have h2 : primeFibAux (f + 1) s.prev s.curr s.remaining = s.prev + s.curr := by
          simp [primeFibAux_succ, hz]
        rw [h1, h2, impIter_done f rfl]
      · have h1 := impStep_continue s hd hz
        have h2 : primeFibAux (f + 1) s.prev s.curr s.remaining =
            primeFibAux f s.curr (s.prev + s.curr)
              (if isPrimeNat (s.prev + s.curr) = true then s.remaining - 1 else s.remaining) := by
          simp [primeFibAux_succ, hz]
        rw [h1, h2]
        exact ih _ rfl hr

/-!
## 9. Imperative tests
-/

example : primeFibImp 0 = 1 := by native_decide
example : primeFibImp 1 = 2 := by native_decide
example : primeFibImp 2 = 3 := by native_decide
example : primeFibImp 3 = 5 := by native_decide
example : primeFibImp 4 = 13 := by native_decide
example : primeFibImp 5 = 89 := by native_decide
example : primeFibImp 6 = 233 := by native_decide
example : primeFibImp 7 = 1597 := by native_decide
example : primeFibImp 8 = 28657 := by native_decide
example : primeFibImp 9 = 514229 := by native_decide
example : primeFibImp 10 = 433494437 := by native_decide

#eval primeFibImp 10

-- PBT (bounded): the imperative loop agrees with the functional search on every input `n ≤ 10`.
example : (List.range 11).all (fun n => primeFibImp n == primeFib n) = true := by native_decide

-- PBT (bounded): the imperative implementation satisfies the postcondition too.
example : (List.range 10).all (fun i => Post_check 45 (i + 1) (primeFibImp (i + 1))) = true := by
  native_decide

-- Randomized PBT: functional and imperative implementations agree.
#eval Plausible.Testable.check (∀ k : Nat, primeFibImp (k % 11) = primeFib (k % 11))

-- Randomized PBT: the imperative answers are prime.
#eval Plausible.Testable.check (∀ k : Nat, decide (Nat.Prime (primeFibImp (k % 10 + 1))) = true)

/-!
## 10. Functional / imperative equivalence
-/

theorem primeFibImp_eq_primeFib (n : Nat) : primeFibImp n = primeFib n := by
  rw [primeFibImp, primeFib, primeFibImp_iter n (fuelOf n)]
  exact impIter_res (fuelOf n) _ rfl rfl

/-- The imperative program satisfies the same postcondition. -/
theorem primeFibImp_correct (n : Nat) (h : Pre n) : Post_prop n (primeFibImp n) := by
  rw [primeFibImp_eq_primeFib]
  exact prime_fib_correct n h

/-- Kernel-checked values of the imperative implementation, via the equivalence theorem. -/
theorem primeFibImp_one : primeFibImp 1 = 2 := by rw [primeFibImp_eq_primeFib, primeFib_one]
theorem primeFibImp_two : primeFibImp 2 = 3 := by rw [primeFibImp_eq_primeFib, primeFib_two]
theorem primeFibImp_three : primeFibImp 3 = 5 := by rw [primeFibImp_eq_primeFib, primeFib_three]
theorem primeFibImp_four : primeFibImp 4 = 13 := by rw [primeFibImp_eq_primeFib, primeFib_four]
theorem primeFibImp_five : primeFibImp 5 = 89 := by rw [primeFibImp_eq_primeFib, primeFib_five]
theorem primeFibImp_six : primeFibImp 6 = 233 := by rw [primeFibImp_eq_primeFib, primeFib_six]
theorem primeFibImp_seven : primeFibImp 7 = 1597 := by rw [primeFibImp_eq_primeFib, primeFib_seven]
theorem primeFibImp_eight : primeFibImp 8 = 28657 := by rw [primeFibImp_eq_primeFib, primeFib_eight]
theorem primeFibImp_nine : primeFibImp 9 = 514229 := by rw [primeFibImp_eq_primeFib, primeFib_nine]
theorem primeFibImp_ten : primeFibImp 10 = 433494437 := by
  rw [primeFibImp_eq_primeFib, primeFib_ten]

theorem primeFibImp_zero : primeFibImp 0 = 1 := by
  rw [primeFibImp_eq_primeFib, primeFib_zero]

end humaneval_39_prime_fib
