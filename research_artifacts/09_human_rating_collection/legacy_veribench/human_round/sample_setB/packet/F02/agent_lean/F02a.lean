import Mathlib

/-!
# HumanEval/39 — `prime_fib`

Translation of the Python program

```python
def prime_fib(n: int):
    import math
    def is_prime(p):
        if p < 2:
            return False
        for k in range(2, min(int(math.sqrt(p)) + 1, p - 1)):
            if p % k == 0:
                return False
        return True
    f = [0, 1]
    while True:
        f.append(f[-1] + f[-2])
        if is_prime(f[-1]):
            n -= 1
        if n == 0:
            return f[-1]
```

`prime_fib n` is the `n`-th natural number that is simultaneously a Fibonacci number
and a prime (1-indexed): `2, 3, 5, 13, 89, 233, 1597, 28657, 514229, 433494437, …`.

## Modelling notes

* `isPrime` is a literal transcription of the Python `is_prime` trial division, including
  the `min (⌊√p⌋ + 1) (p - 1)` upper bound on the tested divisors. `Nat.sqrt` is the exact
  integer square root, which agrees with `int(math.sqrt p)` on every value that occurs here.
  `isPrime_iff_prime` proves that this trial division is exactly `Nat.Prime`.
* The Python `while True` loop is transcribed as a recursion carrying an explicit iteration
  budget `fuel`, because Lean definitions have to be total. `fuelBound n` is a generous
  budget; the loop stops as soon as the `n`-th prime Fibonacci number is found, so the
  budget is irrelevant for every input for which the Python loop terminates. `Pre n`
  records exactly that termination hypothesis (an `n`-th prime Fibonacci number exists and
  is reached within the budget). If the budget were exhausted the implementation returns
  `0`, a value that `Post` rules out.
* Python tests `n == 0` *after* the first `append`, hence `prime_fib(0) = 1`; the
  transcription reproduces this quirk (`primeFib_zero_thm`).
* Everything is modelled in exact integer arithmetic (`Nat`), which is the numeric intent
  of the source program; no floating point is involved.
-/

namespace humaneval_39_prime_fib

open Nat List

/-! ## 1. Functional implementation -/

/-- Transcription of the Python helper `is_prime`: trial division of `p` by every
`k` with `2 ≤ k < min (⌊√p⌋ + 1) (p - 1)`. -/
def isPrime (p : Nat) : Bool :=
  if p < 2 then false
  else !((List.range' 2 (min (Nat.sqrt p + 1) (p - 1) - 2)).any (fun k => decide (p % k = 0)))

/-- The Python statement `if is_prime(f[-1]): n -= 1`, applied to the freshly produced
Fibonacci number `c`. -/
def nextCnt (cnt c : Nat) : Nat := if isPrime c then cnt - 1 else cnt

/-- One pass through the body of the Python `while True` loop.

`primeFibAux fuel cnt a b` runs the loop with `a = fib i`, `b = fib (i+1)` for the current
window, `cnt` the remaining number of prime Fibonacci numbers still to be found and `fuel`
the remaining number of iterations. It returns the Fibonacci number at which the counter
hits `0`, and `0` if the budget is exhausted first. -/
def primeFibAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | fuel + 1, cnt, a, b =>
      if nextCnt cnt (a + b) = 0 then a + b
      else primeFibAux fuel (nextCnt cnt (a + b)) b (a + b)

/-- Iteration budget for the transcribed `while True` loop. It is never exhausted on an
input satisfying `Pre`. -/
def fuelBound (n : Nat) : Nat := n ^ 3 + 100

/-- `primeFib n` is the `n`-th number that is a Fibonacci number and a prime. -/
def primeFib (n : Nat) : Nat := primeFibAux (fuelBound n) n 0 1

/-- `countPrimeFib m` is the number of indices `j < m` such that `fib j` is prime.
It is the exact mathematical counterpart of the Python counter `n -= 1`. -/
def countPrimeFib : Nat → Nat
  | 0 => 0
  | m + 1 => countPrimeFib m + if Nat.Prime (Nat.fib m) then 1 else 0

/-! ## 2. Unit tests -/

#eval isPrime 1
#eval isPrime 2
#eval isPrime 4
#eval isPrime 433494437
#eval primeFib 1
#eval List.map primeFib (List.range 11)

example : isPrime 1 = false := by native_decide
example : isPrime 2 = true := by native_decide
example : isPrime 3 = true := by native_decide
example : isPrime 4 = false := by native_decide
example : isPrime 5 = true := by native_decide
example : isPrime 8 = false := by native_decide
example : isPrime 89 = true := by native_decide
example : isPrime 433494437 = true := by native_decide

-- the Python quirk `prime_fib(0) == 1`
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

example : List.map primeFib (List.range 11) =
    [1, 2, 3, 5, 13, 89, 233, 1597, 28657, 514229, 433494437] := by native_decide

/-! ## 3. Pre- and post-conditions -/

/-- `Pre n`: `n` is a legal input, i.e. `1 ≤ n` (the Python docstring/tests only ever use
positive indices) and the `while True` loop terminates within its iteration budget, i.e.
there really is an `n`-th prime Fibonacci number and it is reached in time. -/
def Pre (n : Nat) : Prop :=
  1 ≤ n ∧ ∃ k, k ≤ fuelBound n ∧ Nat.Prime (Nat.fib k) ∧ countPrimeFib k = n - 1

/-- `Post n v`: `v` is the `n`-th number that is a Fibonacci number and a prime:
`v` is prime, `v` is a Fibonacci number, and exactly `n - 1` prime Fibonacci numbers
occur earlier in the sequence. -/
def Post (n v : Nat) : Prop :=
  Nat.Prime v ∧ ∃ k, Nat.fib k = v ∧ countPrimeFib k = n - 1



/-! ## 4. The transcribed trial division is exactly `Nat.Prime` -/

theorem isPrime_iff_prime (p : Nat) : isPrime p = true ↔ Nat.Prime p := by
  constructor
  · intro h
    have h2 : 2 ≤ p := by
      by_contra hc
      have hlt : p < 2 := by omega
      simp only [isPrime, if_pos hlt] at h
      exact absurd h (by decide)
    rw [Nat.prime_def_lt']
    refine ⟨h2, ?_⟩
    intro m hm2 hmp hmdvd
    have hp1 : p ≠ 1 := by omega
    have hqprime : Nat.Prime (Nat.minFac p) := Nat.minFac_prime hp1
    have hq2 : 2 ≤ Nat.minFac p := Nat.Prime.two_le hqprime
    have hqdvd : Nat.minFac p ∣ p := Nat.minFac_dvd p
    have hmod : p % Nat.minFac p = 0 := Nat.mod_eq_zero_of_dvd hqdvd
    have hqle : Nat.minFac p ≤ m := Nat.minFac_le_of_dvd hm2 hmdvd
    have hqltp : Nat.minFac p < p := lt_of_le_of_lt hqle hmp
    obtain ⟨t, ht⟩ := hqdvd
    have ht2 : 2 ≤ t := by
      by_contra hc
      push_neg at hc
      interval_cases t
      · simp only [Nat.mul_zero] at ht; omega
      · simp only [Nat.mul_one] at ht; omega
    have htdvd : t ∣ p := ⟨Nat.minFac p, by rw [Nat.mul_comm]; exact ht⟩
    have hqt : Nat.minFac p ≤ t := Nat.minFac_le_of_dvd ht2 htdvd
    have hsqrt : Nat.minFac p ≤ Nat.sqrt p := by
      rw [Nat.le_sqrt']
      calc (Nat.minFac p) ^ 2 = Nat.minFac p * Nat.minFac p := by ring
        _ ≤ Nat.minFac p * t := Nat.mul_le_mul_left _ hqt
        _ = p := ht.symm
    have hlt2 : Nat.minFac p < p - 1 := by
      have hA : Nat.minFac p * 2 ≤ p := by
        calc Nat.minFac p * 2 ≤ Nat.minFac p * t := Nat.mul_le_mul_left _ ht2
          _ = p := ht.symm
      have hB : Nat.minFac p + 2 ≤ Nat.minFac p + Nat.minFac p :=
        Nat.add_le_add_left hq2 (Nat.minFac p)
      have hC : Nat.minFac p + Nat.minFac p = Nat.minFac p * 2 := by ring
      omega
    have hmem : Nat.minFac p ∈ List.range' 2 (min (Nat.sqrt p + 1) (p - 1) - 2) := by
      rw [List.mem_range'_1]
      have hB : 3 ≤ min (Nat.sqrt p + 1) (p - 1) := by
        refine le_min ?_ ?_ <;> omega
      exact ⟨hq2, by omega⟩
    simp only [isPrime, if_neg (by omega : ¬ p < 2)] at h
    have hany : (List.range' 2 (min (Nat.sqrt p + 1) (p - 1) - 2)).any
        (fun k => decide (p % k = 0)) = false := by
      by_contra hc
      have ht1 : (List.range' 2 (min (Nat.sqrt p + 1) (p - 1) - 2)).any
          (fun k => decide (p % k = 0)) = true := Bool.of_not_eq_false hc
      rw [ht1] at h
      exact absurd h (by decide)
    rw [List.any_eq_false] at hany
    exact hany _ hmem (decide_eq_true hmod)
  · intro hp
    have h2 : 2 ≤ p := Nat.Prime.two_le hp
    simp only [isPrime, if_neg (by omega : ¬ p < 2)]
    have hkey : ∀ k ∈ List.range' 2 (min (Nat.sqrt p + 1) (p - 1) - 2),
        decide (p % k = 0) = false := by
      intro k hk
      rw [List.mem_range'_1] at hk
      have hkp : k < p := by
        by_cases hB : 2 ≤ min (Nat.sqrt p + 1) (p - 1)
        · have h1 : k < min (Nat.sqrt p + 1) (p - 1) := by omega
          have h2' : min (Nat.sqrt p + 1) (p - 1) ≤ p - 1 := min_le_right _ _
          omega
        · have hz : min (Nat.sqrt p + 1) (p - 1) - 2 = 0 := by omega
          omega
      have hnd : ¬ k ∣ p := by
        intro hkd
        rcases hp.eq_one_or_self_of_dvd k hkd with h1 | h1
        · omega
        · omega
      exact decide_eq_false fun hmod => hnd (Nat.dvd_of_mod_eq_zero hmod)
    have hany : (List.range' 2 (min (Nat.sqrt p + 1) (p - 1) - 2)).any
        (fun k => decide (p % k = 0)) = false := by
      rw [List.any_eq_false]
      intro k hk hc
      rw [hkey k hk] at hc
      exact absurd hc (by decide)
    simp [hany]

/-! ## 5. Counting prime Fibonacci numbers -/

theorem countPrimeFib_succ (m : Nat) :
    countPrimeFib (m + 1) = countPrimeFib m + if Nat.Prime (Nat.fib m) then 1 else 0 := rfl

theorem countPrimeFib_le_succ (n : Nat) : countPrimeFib n ≤ countPrimeFib (n + 1) := by
  rw [countPrimeFib_succ]; omega

theorem countPrimeFib_mono : Monotone countPrimeFib :=
  monotone_nat_of_le_succ countPrimeFib_le_succ

theorem countPrimeFib_lt {k₁ k₂ : Nat} (h : k₁ < k₂) (hp : Nat.Prime (Nat.fib k₁)) :
    countPrimeFib k₁ < countPrimeFib k₂ := by
  have h1 : countPrimeFib (k₁ + 1) = countPrimeFib k₁ + 1 := by
    rw [countPrimeFib_succ, if_pos hp]
  have h2 : countPrimeFib (k₁ + 1) ≤ countPrimeFib k₂ :=
    countPrimeFib_mono (Nat.succ_le_of_lt h)
  omega

theorem countPrimeFib_eq_sum (m : Nat) :
    countPrimeFib m =
      ((List.range m).map (fun j => if Nat.Prime (Nat.fib j) then 1 else 0)).sum := by
  induction m with
  | zero => simp [countPrimeFib]
  | succ m ih =>
    simp only [countPrimeFib_succ, List.range_succ, List.map_append, List.map_singleton,
      List.sum_append, List.sum_singleton, ih]

theorem map_congr_ite {α β : Type} {l : List α} {f g : α → β} (h : ∀ a ∈ l, f a = g a) :
    l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    have ha : f a = g a := h a (List.mem_cons.mpr (Or.inl rfl))
    have has : ∀ b ∈ as, f b = g b := fun b hb => h b (List.mem_cons.mpr (Or.inr hb))
    simp only [List.map_cons, ha, ih has]

/-- The indices `j < 44` for which `fib j` is prime. -/
def primeFibIdxTable : List Nat := [3, 4, 5, 7, 11, 13, 17, 23, 29, 43]

theorem primeFibIdxTable_key : ∀ j ∈ List.range 44,
    (if Nat.Prime (Nat.fib j) then 1 else 0) =
    (if j ∈ primeFibIdxTable then 1 else 0) := by
  intro j hj
  simp only [List.mem_range] at hj
  interval_cases j
  all_goals
    simp only [primeFibIdxTable, List.mem_cons, List.not_mem_nil]
    try norm_num
    try rfl

theorem countPrimeFib_small {m : Nat} (hm : m ≤ 44) :
    countPrimeFib m =
      ((List.range m).map (fun j => if j ∈ primeFibIdxTable then 1 else 0)).sum := by
  rw [countPrimeFib_eq_sum]
  congr 1
  exact map_congr_ite fun j hj =>
    primeFibIdxTable_key j (List.mem_range.mpr (Nat.lt_of_lt_of_le (List.mem_range.mp hj) hm))

theorem countPrimeFib_table (m c : Nat) (hm : m ≤ 44)
    (hc : ((List.range m).map (fun j => if j ∈ primeFibIdxTable then 1 else 0)).sum = c) :
    countPrimeFib m = c := by rw [countPrimeFib_small hm, hc]

theorem countPrimeFib_two : countPrimeFib 2 = 0 :=
  countPrimeFib_table 2 0 (by decide) (by decide)

theorem fib_prime_index {k : Nat} (h : Nat.Prime (Nat.fib k)) : 3 ≤ k := by
  by_contra hc
  have hk : k ≤ 2 := by omega
  interval_cases k
  · exact absurd (Nat.fib_zero ▸ h) Nat.not_prime_zero
  · exact absurd (Nat.fib_one ▸ h) Nat.not_prime_one
  · have h2 : Nat.fib 2 = 1 := by decide
    exact absurd (h2 ▸ h) Nat.not_prime_one


/-! ## 6. The loop invariant -/

theorem nextCnt_eq_zero {cnt c : Nat} (hcnt : 1 ≤ cnt) :
    nextCnt cnt c = 0 ↔ isPrime c = true ∧ cnt = 1 := by
  constructor
  · intro h
    by_cases hi : isPrime c = true
    · refine ⟨hi, ?_⟩
      simp [nextCnt, hi] at h
      omega
    · have hc : nextCnt cnt c = cnt := by simp [nextCnt, hi]
      omega
  · rintro ⟨hi, rfl⟩
    simp only [nextCnt, hi, ite_true]

theorem nextCnt_prime (cnt c : Nat) :
    nextCnt cnt c = if Nat.Prime c then cnt - 1 else cnt := by
  by_cases hi : isPrime c = true
  · have hp : Nat.Prime c := (isPrime_iff_prime c).mp hi
    simp [nextCnt, hi, hp]
  · have hp : ¬ Nat.Prime c := fun hpp => hi ((isPrime_iff_prime c).mpr hpp)
    simp [nextCnt, hi, hp]

/-- One iteration of the loop, expressed on Fibonacci indices. -/
theorem primeFibAux_step (fuel cnt i : Nat) :
    primeFibAux (fuel + 1) cnt (Nat.fib i) (Nat.fib (i + 1)) =
      if nextCnt cnt (Nat.fib (i + 2)) = 0 then Nat.fib (i + 2)
      else primeFibAux fuel (nextCnt cnt (Nat.fib (i + 2))) (Nat.fib (i + 1)) (Nat.fib (i + 2)) := by
  have h1 : primeFibAux (fuel + 1) cnt (Nat.fib i) (Nat.fib (i + 1)) =
      if nextCnt cnt (Nat.fib i + Nat.fib (i + 1)) = 0 then Nat.fib i + Nat.fib (i + 1)
      else primeFibAux fuel (nextCnt cnt (Nat.fib i + Nat.fib (i + 1)))
        (Nat.fib (i + 1)) (Nat.fib i + Nat.fib (i + 1)) := rfl
  have hfib : Nat.fib i + Nat.fib (i + 1) = Nat.fib (i + 2) := Eq.symm (Nat.fib_add_two (n := i))
  rw [h1, hfib]

/-- The counter invariant is preserved by one iteration. -/
theorem countPrimeFib_nextCnt {cnt i N : Nat} (hcnt : 1 ≤ cnt)
    (hN : countPrimeFib (i + 2) + cnt = N) :
    countPrimeFib (i + 3) + nextCnt cnt (Nat.fib (i + 2)) = N := by
  have h3 : i + 3 = (i + 2) + 1 := by omega
  rw [h3, countPrimeFib_succ, nextCnt_prime]
  by_cases hp : Nat.Prime (Nat.fib (i + 2))
  · simp [hp]; omega
  · simp [hp]; omega

/-- Soundness: whenever the loop stops with a nonzero result, that result is a prime
Fibonacci number `fib k` and exactly `N - 1` prime Fibonacci numbers occur before index
`k`, where `N` is the invariant `countPrimeFib (i + 2) + cnt`. -/
theorem primeFibAux_spec {fuel : Nat} : ∀ {cnt i N : Nat},
    1 ≤ cnt →
    countPrimeFib (i + 2) + cnt = N →
    primeFibAux fuel cnt (Nat.fib i) (Nat.fib (i + 1)) ≠ 0 →
    ∃ k, i + 2 ≤ k ∧ Nat.fib k = primeFibAux fuel cnt (Nat.fib i) (Nat.fib (i + 1)) ∧
      Nat.Prime (Nat.fib k) ∧ countPrimeFib k = N - 1 := by
  induction fuel with
  | zero => intro cnt i N _ _ hres; exfalso; exact hres rfl
  | succ fuel ih =>
      intro cnt i N hcnt hN hres
      have hstep := primeFibAux_step fuel cnt i
      rw [hstep] at hres ⊢
      by_cases hz : nextCnt cnt (Nat.fib (i + 2)) = 0
      · simp only [hz, ite_true] at hres ⊢
        obtain ⟨hi, hc1⟩ := (nextCnt_eq_zero hcnt).mp hz
        have hp : Nat.Prime (Nat.fib (i + 2)) := (isPrime_iff_prime _).mp hi
        refine ⟨i + 2, le_refl _, rfl, hp, ?_⟩
        omega
      · simp only [hz, ite_false] at hres ⊢
        have hcnt' : 1 ≤ nextCnt cnt (Nat.fib (i + 2)) := Nat.pos_of_ne_zero hz
        have hN' : countPrimeFib ((i + 1) + 2) + nextCnt cnt (Nat.fib (i + 2)) = N := by
          have h3 : (i + 1) + 2 = i + 3 := by omega
          rw [h3]
          exact countPrimeFib_nextCnt hcnt hN
        obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih hcnt' hN' hres
        exact ⟨k, by omega, hk2, hk3, hk4⟩

/-- Completeness: if the `n`-th prime Fibonacci number is reached within the budget, the
loop does not run out of fuel. -/
theorem primeFibAux_ne_zero {fuel : Nat} : ∀ {cnt i N : Nat},
    1 ≤ cnt →
    countPrimeFib (i + 2) + cnt = N →
    (∃ k, i + 2 ≤ k ∧ k ≤ i + 1 + fuel ∧ Nat.Prime (Nat.fib k) ∧ countPrimeFib k = N - 1) →
    primeFibAux fuel cnt (Nat.fib i) (Nat.fib (i + 1)) ≠ 0 := by
  induction fuel with
  | zero =>
    intro cnt i N _ _ hw
    obtain ⟨k, hk1, hk2, _, _⟩ := hw
    omega
  | succ fuel ih =>
      intro cnt i N hcnt hN hw
      rw [primeFibAux_step fuel cnt i]
      by_cases hz : nextCnt cnt (Nat.fib (i + 2)) = 0
      · simp only [hz, ite_true]
        obtain ⟨hi, _⟩ := (nextCnt_eq_zero hcnt).mp hz
        have hp : Nat.Prime (Nat.fib (i + 2)) := (isPrime_iff_prime _).mp hi
        exact Nat.Prime.ne_zero hp
      · simp only [hz, ite_false]
        obtain ⟨k, hk1, hk2, hk3, hk4⟩ := hw
        have hcnt' : 1 ≤ nextCnt cnt (Nat.fib (i + 2)) := Nat.pos_of_ne_zero hz
        have hN' : countPrimeFib ((i + 1) + 2) + nextCnt cnt (Nat.fib (i + 2)) = N := by
          have h3 : (i + 1) + 2 = i + 3 := by omega
          rw [h3]
          exact countPrimeFib_nextCnt hcnt hN
        by_cases hke : k = i + 2
        · subst hke
          have hc : countPrimeFib (i + 2) = N - 1 := hk4
          have hc1 : cnt = 1 := by omega
          have hi : isPrime (Nat.fib (i + 2)) = true := (isPrime_iff_prime _).mpr hk3
          have hzz : nextCnt cnt (Nat.fib (i + 2)) = 0 := by simp [nextCnt, hi, hc1]
          contradiction
        · have hk1' : (i + 1) + 2 ≤ k := by omega
          have hk2' : k ≤ (i + 1) + 1 + fuel := by omega
          exact ih hcnt' hN' ⟨k, hk1', hk2', hk3, hk4⟩

/-! ## 7. Consequences for `primeFib` -/

theorem primeFib_spec {n : Nat} (h : Pre n) :
    ∃ k, Nat.Prime (Nat.fib k) ∧ Nat.fib k = primeFib n ∧ countPrimeFib k = n - 1 := by
  obtain ⟨hn, k, hk, hkp, hkc⟩ := h
  have hk3 : 3 ≤ k := fib_prime_index hkp
  have hN : countPrimeFib (0 + 2) + n = n := by
    rw [Nat.zero_add, countPrimeFib_two]
    omega
  have hne : primeFibAux (fuelBound n) n (Nat.fib 0) (Nat.fib (0 + 1)) ≠ 0 :=
    primeFibAux_ne_zero hn hN
      ⟨k, by omega, by show k ≤ 0 + 1 + fuelBound n; omega, hkp, hkc⟩
  obtain ⟨j, _, hjfib, hjp, hjc⟩ := primeFibAux_spec hn hN hne
  have heq : Nat.fib j = primeFib n := by
    have hrew : primeFib n =
        primeFibAux (fuelBound n) n (Nat.fib 0) (Nat.fib (0 + 1)) := by
      simp [primeFib, Nat.fib_zero, Nat.fib_one]
    rw [hrew]
    exact hjfib
  exact ⟨j, hjp, heq, hjc⟩

theorem primeFib_post {n : Nat} (h : Pre n) : Post n (primeFib n) := by
  obtain ⟨k, hk1, hk2, hk3⟩ := primeFib_spec h
  exact ⟨hk2 ▸ hk1, k, hk2, hk3⟩

/-- `Post n` determines the returned value uniquely. -/
theorem post_unique {n v₁ v₂ : Nat} (h₁ : Post n v₁) (h₂ : Post n v₂) : v₁ = v₂ := by
  obtain ⟨hp₁, k₁, hk₁, hc₁⟩ := h₁
  obtain ⟨hp₂, k₂, hk₂, hc₂⟩ := h₂
  have hp₁' : Nat.Prime (Nat.fib k₁) := hk₁ ▸ hp₁
  have hp₂' : Nat.Prime (Nat.fib k₂) := hk₂ ▸ hp₂
  have hkk : k₁ = k₂ := by
    rcases lt_trichotomy k₁ k₂ with hlt | heq | hgt
    · exact absurd (countPrimeFib_lt hlt hp₁') (by rw [hc₁, hc₂]; exact Nat.lt_irrefl _)
    · exact heq
    · exact absurd (countPrimeFib_lt hgt hp₂') (by rw [hc₂, hc₁]; exact Nat.lt_irrefl _)
  rw [← hk₁, ← hk₂, hkk]

theorem primeFib_eq_of_index {n k v : Nat} (hn : 1 ≤ n) (hk : k ≤ fuelBound n)
    (hp : Nat.Prime (Nat.fib k)) (hf : Nat.fib k = v) (hc : countPrimeFib k = n - 1) :
    primeFib n = v :=
  post_unique (primeFib_post ⟨hn, k, hk, hp, hc⟩) ⟨hf ▸ hp, k, hf, hc⟩


/-! ## 8. The values of the Python docstring / test suite, proved in the kernel -/

theorem primeFib_val_0 : primeFib 0 = 1 := by decide

theorem primeFib_val_1 : primeFib 1 = 2 :=
  primeFib_eq_of_index (n := 1) (k := 3) (v := 2) (by decide) (by decide) (by norm_num)
    (by decide) (countPrimeFib_table 3 0 (by decide) (by decide))

theorem primeFib_val_2 : primeFib 2 = 3 :=
  primeFib_eq_of_index (n := 2) (k := 4) (v := 3) (by decide) (by decide) (by norm_num)
    (by decide) (countPrimeFib_table 4 1 (by decide) (by decide))

theorem primeFib_val_3 : primeFib 3 = 5 :=
  primeFib_eq_of_index (n := 3) (k := 5) (v := 5) (by decide) (by decide) (by norm_num)
    (by decide) (countPrimeFib_table 5 2 (by decide) (by decide))

theorem primeFib_val_4 : primeFib 4 = 13 :=
  primeFib_eq_of_index (n := 4) (k := 7) (v := 13) (by decide) (by decide) (by norm_num)
    (by decide) (countPrimeFib_table 7 3 (by decide) (by decide))

theorem primeFib_val_5 : primeFib 5 = 89 :=
  primeFib_eq_of_index (n := 5) (k := 11) (v := 89) (by decide) (by decide) (by norm_num)
    (by decide) (countPrimeFib_table 11 4 (by decide) (by decide))

theorem primeFib_val_6 : primeFib 6 = 233 :=
  primeFib_eq_of_index (n := 6) (k := 13) (v := 233) (by decide) (by decide) (by norm_num)
    (by decide) (countPrimeFib_table 13 5 (by decide) (by decide))

theorem primeFib_val_7 : primeFib 7 = 1597 :=
  primeFib_eq_of_index (n := 7) (k := 17) (v := 1597) (by decide) (by decide) (by norm_num)
    (by decide) (countPrimeFib_table 17 6 (by decide) (by decide))

theorem primeFib_val_8 : primeFib 8 = 28657 :=
  primeFib_eq_of_index (n := 8) (k := 23) (v := 28657) (by decide) (by decide) (by norm_num)
    (by decide) (countPrimeFib_table 23 7 (by decide) (by decide))

theorem primeFib_val_9 : primeFib 9 = 514229 :=
  primeFib_eq_of_index (n := 9) (k := 29) (v := 514229) (by decide) (by decide) (by norm_num)
    (by decide) (countPrimeFib_table 29 8 (by decide) (by decide))

theorem primeFib_val_10 : primeFib 10 = 433494437 :=
  primeFib_eq_of_index (n := 10) (k := 43) (v := 433494437) (by decide) (by decide)
    (by norm_num) (by decide) (countPrimeFib_table 43 9 (by decide) (by decide))

/-- The Fibonacci index at which the `n`-th prime Fibonacci number occurs, for `1 ≤ n ≤ 10`. -/
def preWitness : Nat → Nat
  | 1 => 3
  | 2 => 4
  | 3 => 5
  | 4 => 7
  | 5 => 11
  | 6 => 13
  | 7 => 17
  | 8 => 23
  | 9 => 29
  | 10 => 43
  | _ => 0

/-- `Pre` is satisfiable: it holds for every index tested by the Python test suite. -/
theorem primeFib_pre_10 : ∀ n, 1 ≤ n → n ≤ 10 → Pre n := by
  intro n hn1 hn2
  interval_cases n
  all_goals
    refine ⟨by decide, preWitness n, by decide, ?_, ?_⟩
    · simp only [preWitness]; norm_num
    · simp only [preWitness]; rw [countPrimeFib_small (by decide)]; decide

/-! ## 9. Properties of the implementation -/

/-- The transcribed trial division is exactly primality. -/
def isPrime_correct_prop (p : Nat) : Prop := isPrime p = true ↔ Nat.Prime p

theorem isPrime_correct_thm (p : Nat) : isPrime_correct_prop p := isPrime_iff_prime p

/-- The returned number is prime. -/
def primeFib_prime_prop (n : Nat) : Prop := Pre n → Nat.Prime (primeFib n)

theorem primeFib_prime_thm (n : Nat) : primeFib_prime_prop n := by
  intro h
  obtain ⟨k, hk1, hk2, _⟩ := primeFib_spec h
  exact hk2 ▸ hk1

/-- The returned number is a Fibonacci number. -/
def primeFib_isFib_prop (n : Nat) : Prop := Pre n → ∃ k, Nat.fib k = primeFib n

theorem primeFib_isFib_thm (n : Nat) : primeFib_isFib_prop n := by
  intro h
  obtain ⟨k, _, hk2, _⟩ := primeFib_spec h
  exact ⟨k, hk2⟩

/-- The returned number is the `n`-th prime Fibonacci number: exactly `n - 1` prime
Fibonacci numbers occur at earlier indices. -/
def primeFib_nth_prop (n : Nat) : Prop :=
  Pre n → ∃ k, Nat.fib k = primeFib n ∧ countPrimeFib k = n - 1

theorem primeFib_nth_thm (n : Nat) : primeFib_nth_prop n := by
  intro h
  obtain ⟨k, _, hk2, hk3⟩ := primeFib_spec h
  exact ⟨k, hk2, hk3⟩

/-- The returned number is at least two. -/
def primeFib_two_le_prop (n : Nat) : Prop := Pre n → 2 ≤ primeFib n

theorem primeFib_two_le_thm (n : Nat) : primeFib_two_le_prop n := by
  intro h
  exact Nat.Prime.two_le (primeFib_prime_thm n h)

/-- The sequence of prime Fibonacci numbers is strictly increasing. -/
def primeFib_strictMono_prop (n : Nat) : Prop :=
  Pre n → Pre (n + 1) → primeFib n < primeFib (n + 1)

theorem primeFib_strictMono_thm (n : Nat) : primeFib_strictMono_prop n := by
  intro h1 h2
  obtain ⟨hn, _⟩ := h1
  obtain ⟨k1, hk1p, hk1v, hk1c⟩ := primeFib_spec h1
  obtain ⟨k2, hk2p, hk2v, hk2c⟩ := primeFib_spec h2
  have hk12 : k1 < k2 := by
    by_contra hc
    push_neg at hc
    have hle : countPrimeFib k2 ≤ countPrimeFib k1 := countPrimeFib_mono hc
    omega
  have h3 : 2 ≤ k1 := Nat.le_trans (by decide) (fib_prime_index hk1p)
  have hlt : Nat.fib k1 < Nat.fib k2 := (Nat.fib_lt_fib h3).mpr hk12
  rw [← hk1v, ← hk2v]
  exact hlt

/-- The Python quirk `prime_fib(0) == 1`. -/
def primeFib_zero_prop : Prop := primeFib 0 = 1

theorem primeFib_zero_thm : primeFib_zero_prop := primeFib_val_0

/-- The ten values asserted by the Python `check` function. -/
def primeFib_values_prop : Prop :=
  primeFib 1 = 2 ∧ primeFib 2 = 3 ∧ primeFib 3 = 5 ∧ primeFib 4 = 13 ∧ primeFib 5 = 89 ∧
    primeFib 6 = 233 ∧ primeFib 7 = 1597 ∧ primeFib 8 = 28657 ∧ primeFib 9 = 514229 ∧
    primeFib 10 = 433494437

theorem primeFib_values_thm : primeFib_values_prop :=
  ⟨primeFib_val_1, primeFib_val_2, primeFib_val_3, primeFib_val_4, primeFib_val_5,
    primeFib_val_6, primeFib_val_7, primeFib_val_8, primeFib_val_9, primeFib_val_10⟩

/-! ## 10. Post-condition -/

/-- The post-condition, as a conjunction of the properties above. -/
def Post_prop (n : Nat) : Prop :=
  primeFib_prime_prop n ∧ primeFib_isFib_prop n ∧ primeFib_nth_prop n ∧
    primeFib_two_le_prop n ∧ primeFib_strictMono_prop n

theorem Post_thm (n : Nat) : Post_prop n :=
  ⟨primeFib_prime_thm n, primeFib_isFib_thm n, primeFib_nth_thm n, primeFib_two_le_thm n,
    primeFib_strictMono_thm n⟩

end humaneval_39_prime_fib
