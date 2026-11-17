import Mathlib

/-!
# HumanEval 39 — prime Fibonacci numbers

`prime_fib n` is the `n`-th Fibonacci number that is also prime (1-indexed).
The sequence begins

```
2, 3, 5, 13, 89, 233, 1597, 28657, 514229, 433494437, …
```

which are `F₃, F₄, F₅, F₇, F₁₁, F₁₃, F₁₇, F₂₃, F₂₉, F₄₃, …`
(`F₀ = 0`, `F₁ = 1`, `F₂ = 1`). `F₁ = F₂ = 1` is not prime, so the count
starts at `2`.

The Python source walks the Fibonacci recurrence and uses a trial-division
primality test up to `⌊√p⌋`. That test agrees with `Nat.Prime` on every
natural number (IEEE-754 `math.sqrt` is exact for every integer that this
search actually builds). It is unknown whether infinitely many prime
Fibonacci numbers exist, so the executable search is fuel-bounded. The fuel
reaches `F₄₃`, which is enough for every HumanEval test (`n = 1 .. 10`).
`Pre` is exactly the domain on which that search is guaranteed to have found
the mathematical `n`-th prime Fibonacci number.

For `n = 0` the Python loop returns `1` (it emits `F₂` before any prime is
seen and the counter is already `0`). The same edge is reproduced here.
-/

namespace humaneval_39_prime_fib

open Nat

/-! ## Primality test (Python `is_prime`) -/

/-- Trial division from `k` up to (but not including) `stop`, matching
`for k in range(start, stop)`. -/
def noDivisorFrom (p k stop : Nat) : Bool :=
  if hk : k < stop then
    if hdiv : p % k = 0 then
      false
    else
      noDivisorFrom p (k + 1) stop
  else
    true
termination_by stop - k

/-- Python `is_prime`. Returns false for `p < 2`. Otherwise checks that no
`k` with `2 ≤ k < min(⌊√p⌋ + 1, p - 1)` divides `p`. -/
def isPrime (p : Nat) : Bool :=
  if p < 2 then
    false
  else
    noDivisorFrom p 2 (min (Nat.sqrt p + 1) (p - 1))

/-- `Fₖ` is a prime number. -/
abbrev IsPrimeFib (k : Nat) : Prop := (Nat.fib k).Prime

instance : DecidablePred IsPrimeFib := fun _ => inferInstance

/-! ## Functional implementation -/

/-- How many Fibonacci steps the executable search may take.
Iteration `t = 1, …, searchFuel` emits `F_{t+1}`, so `searchFuel = 42`
emits `F₂, …, F₄₃` and therefore every prime Fibonacci number among the
HumanEval tests. -/
def searchFuel : Nat := 42

/-- One Python loop iteration, with an explicit fuel.
`prev = Fᵢ`, `curr = Fᵢ₊₁`, and `remaining` is how many prime Fibonacci
numbers are still required. The value `0` is returned only when the fuel
is spent before that many primes appear. -/
def primeFibLoop (prev curr remaining fuel : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 =>
    let next := prev + curr
    let remaining' := if isPrime next then remaining - 1 else remaining
    if remaining' = 0 then
      next
    else
      primeFibLoop curr next remaining' fuel

/-- The `n`-th prime Fibonacci number for every `n` satisfying `Pre`,
and `1` when `n = 0` (the Python edge case). -/
def primeFib (n : Nat) : Nat :=
  primeFibLoop 0 1 n searchFuel

/-! ## Unit tests -/

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
example : primeFib 0 = 1 := by native_decide

#eval primeFib 1
#eval primeFib 2
#eval primeFib 3
#eval primeFib 4
#eval primeFib 5
#eval primeFib 6
#eval primeFib 7
#eval primeFib 8
#eval primeFib 9
#eval primeFib 10

/-! ## Pre-condition -/

/-- `n` is positive and at least `n` prime Fibonacci numbers occur at
indices `< searchFuel + 2` (that is, among `F₀, …, F_{searchFuel+1}`).
On this domain `primeFib n` is the mathematical `n`-th prime Fibonacci number. -/
def Pre (n : Nat) : Prop :=
  0 < n ∧ n ≤ Nat.count IsPrimeFib (searchFuel + 2)

/-! ## Primality agreement -/

private theorem noDivisorFrom_of_forall {p k stop : Nat}
    (h : ∀ m, k ≤ m → m < stop → ¬ m ∣ p) : noDivisorFrom p k stop = true := by
  rw [noDivisorFrom]
  split
  · rename_i hk
    have hnd : ¬ p % k = 0 := by
      simpa [Nat.dvd_iff_mod_eq_zero] using h k le_rfl hk
    simp only [hnd, dite_false]
    exact noDivisorFrom_of_forall (fun m hm1 hm2 => h m (by omega) hm2)
  · rfl
termination_by stop - k
decreasing_by
  simp_wf
  omega

private theorem forall_of_noDivisorFrom {p k stop : Nat}
    (h : noDivisorFrom p k stop = true) {m : Nat} (hm1 : k ≤ m) (hm2 : m < stop) :
    ¬ m ∣ p := by
  rw [noDivisorFrom] at h
  split at h
  · rename_i hk
    by_cases hdiv : p % k = 0
    · simp [hdiv] at h
    · simp only [hdiv, dite_false] at h
      by_cases hkm : m = k
      · subst hkm
        simpa [Nat.dvd_iff_mod_eq_zero] using hdiv
      · exact forall_of_noDivisorFrom h (by omega) hm2
  · rename_i hk
    omega
termination_by stop - k
decreasing_by
  simp_wf
  omega

private theorem noDivisorFrom_iff (p k stop : Nat) :
    noDivisorFrom p k stop = true ↔ ∀ m, k ≤ m → m < stop → ¬ m ∣ p :=
  ⟨fun h _ hm1 hm2 => forall_of_noDivisorFrom h hm1 hm2, noDivisorFrom_of_forall⟩

private theorem pred_sq_gt {p : Nat} (hp : 4 ≤ p) : p < (p - 1) * (p - 1) := by
  have hz : (p : ℤ) < ((p : ℤ) - 1) * ((p : ℤ) - 1) := by
    have hp' : (4 : ℤ) ≤ p := by exact_mod_cast hp
    nlinarith
  have hnonneg : 1 ≤ p := by omega
  have hcast : ((p - 1 : Nat) : ℤ) = (p : ℤ) - 1 := by
    exact Nat.cast_sub hnonneg
  have hmul : (((p - 1) * (p - 1) : Nat) : ℤ) = ((p : ℤ) - 1) * ((p : ℤ) - 1) := by
    rw [Nat.cast_mul, hcast]
  have : (p : ℤ) < (((p - 1) * (p - 1) : Nat) : ℤ) := by
    rw [hmul]
    exact hz
  exact_mod_cast this

private theorem sqrt_lt_pred_of_ge_four {p : Nat} (hp : 4 ≤ p) : Nat.sqrt p < p - 1 := by
  rw [Nat.sqrt_lt]
  exact pred_sq_gt hp

/-- The Python trial test accepts `p` if and only if `p` is prime. -/
def isPrime_correct_prop (p : Nat) : Prop :=
  isPrime p = true ↔ p.Prime

theorem isPrime_correct_thm (p : Nat) : isPrime_correct_prop p := by
  unfold isPrime_correct_prop isPrime
  by_cases hp : p < 2
  · have hnot : ¬ p.Prime := by
      interval_cases p
      · exact Nat.not_prime_zero
      · exact Nat.not_prime_one
    simp [hp, hnot]
  · have hp2 : 2 ≤ p := Nat.not_lt.mp hp
    simp only [hp, ite_false]
    rw [noDivisorFrom_iff, Nat.prime_def_le_sqrt]
    constructor
    · intro hdiv
      refine ⟨hp2, fun m hm2 hsqrt => ?_⟩
      apply hdiv m hm2
      apply lt_min
      · exact Nat.lt_succ_of_le hsqrt
      · by_cases hp4 : 4 ≤ p
        · exact lt_of_le_of_lt hsqrt (sqrt_lt_pred_of_ge_four hp4)
        · interval_cases p
          · have hsqrt2 : Nat.sqrt 2 = 1 := by decide
            have hmle : m ≤ 1 := by simpa [hsqrt2] using hsqrt
            omega
          · have hsqrt3 : Nat.sqrt 3 = 1 := by decide
            have hmle : m ≤ 1 := by simpa [hsqrt3] using hsqrt
            omega
    · intro ⟨_, hdiv⟩ m hm2 hmstop
      have hsqrt : m ≤ Nat.sqrt p :=
        Nat.le_of_lt_succ (lt_of_lt_of_le hmstop (min_le_left _ _))
      exact hdiv m hm2 hsqrt

theorem isPrime_iff (p : Nat) : isPrime p = true ↔ p.Prime :=
  isPrime_correct_thm p

/-! ## Loop invariant: the search returns the `n`-th prime Fibonacci number -/

private theorem count_two_eq_zero : Nat.count IsPrimeFib 2 = 0 := by
  simp [Nat.count_succ, Nat.count_zero, IsPrimeFib, fib_zero, fib_one,
    Nat.not_prime_zero, Nat.not_prime_one]

private theorem count_card_ge {B n : Nat} (h : n ≤ Nat.count IsPrimeFib B)
    (hf : (setOf IsPrimeFib).Finite) : n ≤ hf.toFinset.card :=
  le_trans h (Nat.count_le_card hf B)

private theorem nth_index_lt_card {n : Nat} (hn : Pre n)
    (hf : (setOf IsPrimeFib).Finite) : n - 1 < hf.toFinset.card := by
  exact Nat.lt_of_lt_of_le (Nat.sub_lt hn.1 Nat.one_pos) (count_card_ge hn.2 hf)

/-- Enough fuel to hit a cumulative prime-Fibonacci count. -/
private theorem primeFibLoop_eq_nth :
    ∀ {fuel i remaining : Nat},
      0 < remaining →
      Nat.count IsPrimeFib (i + 2) + remaining ≤ Nat.count IsPrimeFib (i + 2 + fuel) →
      primeFibLoop (Nat.fib i) (Nat.fib (i + 1)) remaining fuel =
        Nat.fib (Nat.nth IsPrimeFib (Nat.count IsPrimeFib (i + 2) + remaining - 1)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i remaining hrem hfuel
    have : remaining = 0 := by
      have hle : Nat.count IsPrimeFib (i + 2) + remaining ≤ Nat.count IsPrimeFib (i + 2) := by
        simpa using hfuel
      omega
    omega
  | succ fuel ih =>
    intro i remaining hrem hfuel
    rw [primeFibLoop]
    have hadd : Nat.fib i + Nat.fib (i + 1) = Nat.fib (i + 2) := by
      simpa [Nat.add_comm] using (Nat.fib_add_two (n := i)).symm
    simp only [hadd]
    have hprime : isPrime (Nat.fib (i + 2)) = true ↔ IsPrimeFib (i + 2) := isPrime_iff _
    by_cases hp : IsPrimeFib (i + 2)
    · have hbool : isPrime (Nat.fib (i + 2)) = true := hprime.mpr hp
      simp only [hbool, ite_true]
      have hcount_succ : Nat.count IsPrimeFib (i + 3) = Nat.count IsPrimeFib (i + 2) + 1 := by
        rw [Nat.count_succ]
        simp [hp]
      by_cases hrem1 : remaining = 1
      · simp only [hrem1, Nat.sub_self, ite_true]
        have hnth : Nat.nth IsPrimeFib (Nat.count IsPrimeFib (i + 2)) = i + 2 :=
          Nat.nth_count hp
        have hidx : Nat.count IsPrimeFib (i + 2) + 1 - 1 = Nat.count IsPrimeFib (i + 2) := by
          omega
        simp [hidx, hnth]
      · have hrem' : 0 < remaining - 1 := by omega
        have hne : remaining - 1 ≠ 0 := by omega
        simp only [hne, ite_false]
        have hfuel' : Nat.count IsPrimeFib ((i + 1) + 2) + (remaining - 1) ≤
            Nat.count IsPrimeFib ((i + 1) + 2 + fuel) := by
          have hc : Nat.count IsPrimeFib ((i + 1) + 2) = Nat.count IsPrimeFib (i + 2) + 1 := by
            simpa [show (i + 1) + 2 = i + 3 by omega] using hcount_succ
          have hr : Nat.count IsPrimeFib (i + 2) + 1 + (remaining - 1) =
              Nat.count IsPrimeFib (i + 2) + remaining := by omega
          have hend : (i + 1) + 2 + fuel = i + 2 + (fuel + 1) := by omega
          simpa [hc, hr, hend] using hfuel
        have ih' := ih (i := i + 1) (remaining := remaining - 1) hrem' hfuel'
        have htarget : Nat.count IsPrimeFib ((i + 1) + 2) + (remaining - 1) - 1 =
            Nat.count IsPrimeFib (i + 2) + remaining - 1 := by
          have hc : Nat.count IsPrimeFib ((i + 1) + 2) = Nat.count IsPrimeFib (i + 2) + 1 := by
            simpa [show (i + 1) + 2 = i + 3 by omega] using hcount_succ
          omega
        simpa [htarget] using ih'
    · have hbool : isPrime (Nat.fib (i + 2)) = false := by
        cases hbit : isPrime (Nat.fib (i + 2))
        · rfl
        · exact absurd (hprime.mp hbit) hp
      have hcount_same : Nat.count IsPrimeFib (i + 3) = Nat.count IsPrimeFib (i + 2) := by
        rw [Nat.count_succ]
        simp [hp]
      simp only [hbool, Bool.cond_false]
      have hne : remaining ≠ 0 := by omega
      simp only [hne, ite_false]
      have hfuel' : Nat.count IsPrimeFib ((i + 1) + 2) + remaining ≤
          Nat.count IsPrimeFib ((i + 1) + 2 + fuel) := by
        have hc : Nat.count IsPrimeFib ((i + 1) + 2) = Nat.count IsPrimeFib (i + 2) := by
          simpa [show (i + 1) + 2 = i + 3 by omega] using hcount_same
        have hend : (i + 1) + 2 + fuel = i + 2 + fuel + 1 := by omega
        simpa [hc, hend] using hfuel
      have ih' := ih (i := i + 1) (remaining := remaining) hrem hfuel'
      have htarget : Nat.count IsPrimeFib ((i + 1) + 2) + remaining - 1 =
          Nat.count IsPrimeFib (i + 2) + remaining - 1 := by
        have hc : Nat.count IsPrimeFib ((i + 1) + 2) = Nat.count IsPrimeFib (i + 2) := by
          simpa [show (i + 1) + 2 = i + 3 by omega] using hcount_same
        omega
      simpa [htarget] using ih'

theorem primeFib_eq_nth {n : Nat} (hn : Pre n) :
    primeFib n = Nat.fib (Nat.nth IsPrimeFib (n - 1)) := by
  unfold primeFib
  have hfuel : Nat.count IsPrimeFib (0 + 2) + n ≤ Nat.count IsPrimeFib (0 + 2 + searchFuel) := by
    simpa [count_two_eq_zero, show 0 + 2 + searchFuel = searchFuel + 2 by omega] using hn.2
  have hloop := primeFibLoop_eq_nth (fuel := searchFuel) (i := 0) (remaining := n) hn.1 hfuel
  simpa [count_two_eq_zero, Nat.zero_add] using hloop

/-! ## Properties -/

def prime_result_prop (n : Nat) : Prop := (primeFib n).Prime

def fib_result_prop (n : Nat) : Prop := ∃ k : Nat, primeFib n = Nat.fib k

def nth_result_prop (n : Nat) : Prop :=
  primeFib n = Nat.fib (Nat.nth IsPrimeFib (n - 1))

/-- `primeFib n` is the value `Fₖ` where exactly `n - 1` prime Fibonacci
numbers have a strictly smaller index, and `Fₖ` itself is prime. -/
def order_result_prop (n : Nat) : Prop :=
  ∃ k, primeFib n = Nat.fib k ∧ IsPrimeFib k ∧
    Nat.count IsPrimeFib k = n - 1 ∧ Nat.count IsPrimeFib (k + 1) = n

def ge_two_prop (n : Nat) : Prop := 2 ≤ primeFib n

/-- Later admissible inputs return strictly larger prime Fibonacci numbers. -/
def mono_prop (n m : Nat) : Prop := n < m → primeFib n < primeFib m

theorem prime_result_thm {n : Nat} (hn : Pre n) : prime_result_prop n := by
  unfold prime_result_prop
  rw [primeFib_eq_nth hn]
  exact Nat.nth_mem (n - 1) (fun hf => nth_index_lt_card hn hf)

theorem fib_result_thm {n : Nat} (hn : Pre n) : fib_result_prop n := by
  unfold fib_result_prop
  exact ⟨Nat.nth IsPrimeFib (n - 1), primeFib_eq_nth hn⟩

theorem nth_result_thm {n : Nat} (hn : Pre n) : nth_result_prop n :=
  primeFib_eq_nth hn

theorem order_result_thm {n : Nat} (hn : Pre n) : order_result_prop n := by
  unfold order_result_prop
  refine ⟨Nat.nth IsPrimeFib (n - 1), primeFib_eq_nth hn, ?_, ?_, ?_⟩
  · exact Nat.nth_mem (n - 1) (fun hf => nth_index_lt_card hn hf)
  · exact Nat.count_nth (fun hf => nth_index_lt_card hn hf)
  · have hsucc := Nat.count_nth_succ (p := IsPrimeFib) (n := n - 1)
      (fun hf => nth_index_lt_card hn hf)
    simpa [Nat.sub_add_cancel (Nat.one_le_of_lt hn.1)] using hsucc

theorem ge_two_thm {n : Nat} (hn : Pre n) : ge_two_prop n := by
  unfold ge_two_prop
  exact Nat.Prime.two_le (prime_result_thm hn)

private theorem nth_ge_two {n : Nat} (hn : Pre n) : 2 ≤ Nat.nth IsPrimeFib (n - 1) := by
  have hp : IsPrimeFib (Nat.nth IsPrimeFib (n - 1)) :=
    Nat.nth_mem (n - 1) (fun hf => nth_index_lt_card hn hf)
  have h2 : 2 ≤ Nat.fib (Nat.nth IsPrimeFib (n - 1)) := Nat.Prime.two_le hp
  by_contra hlt
  have : Nat.nth IsPrimeFib (n - 1) ≤ 1 := by omega
  interval_cases hidx : Nat.nth IsPrimeFib (n - 1)
  · simp [IsPrimeFib, fib_zero, Nat.not_prime_zero] at hp
  · simp [IsPrimeFib, fib_one, Nat.not_prime_one] at hp

theorem mono_thm {n m : Nat} (hn : Pre n) (hm : Pre m) (hnm : n < m) : mono_prop n m := by
  unfold mono_prop
  intro _
  rw [primeFib_eq_nth hn, primeFib_eq_nth hm]
  have hidx : Nat.nth IsPrimeFib (n - 1) < Nat.nth IsPrimeFib (m - 1) := by
    apply Nat.nth_lt_nth'
    · exact Nat.sub_lt_sub_right (Nat.one_le_of_lt hn.1) hnm
    · intro hf
      exact Nat.lt_of_lt_of_le (Nat.sub_lt hm.1 Nat.one_pos) (count_card_ge hm.2 hf)
  exact (Nat.fib_lt_fib (nth_ge_two hn)).2 hidx

/-- `n = 0` reproduces the Python edge: the first emitted Fibonacci number
`F₂ = 1` is returned because the counter is already zero. -/
theorem primeFib_zero_thm : primeFib 0 = 1 := by
  unfold primeFib
  have hfuel : searchFuel = 41 + 1 := by decide
  rw [hfuel, primeFibLoop]
  have hone : isPrime (0 + 1) = false := by
    unfold isPrime
    simp
  simp [hone]

/-! ## Post-condition -/

def Post_prop (n : Nat) : Prop :=
  prime_result_prop n ∧ fib_result_prop n ∧ nth_result_prop n ∧
    order_result_prop n ∧ ge_two_prop n

/-! ## Property-based tests

Executable checks of every `_prop` and of `Post_prop`.
`native_decide` compiles the same trial division the implementation uses.
Plausible samples the admissible range `Fin 11` (values `0, …, 10`); the
guard `0 < n` drops the Python `n = 0` edge, which is specified separately.
-/

/-- Executable form of `order_result_prop`: `r` is prime, equals some `Fₖ`
below the search limit, exactly `n - 1` smaller prime Fibonacci numbers
exist in that range, and `Fₖ` itself is one of them. -/
private def orderExec (n r : Nat) : Bool :=
  isPrime r &&
    ((List.range (searchFuel + 2)).countP fun k =>
      isPrime (Nat.fib k) && Nat.fib k < r) == n - 1 &&
    ((List.range (searchFuel + 2)).any fun k =>
      isPrime (Nat.fib k) && Nat.fib k == r)

example : (List.range 11).all (fun n =>
    n == 0 || decide ((primeFib n).Prime)) = true := by
  native_decide

example : (List.range 11).all (fun n =>
    n == 0 || decide (2 ≤ primeFib n)) = true := by
  native_decide

example : (List.range 11).all (fun n =>
    n == 0 || orderExec n (primeFib n)) = true := by
  native_decide

example : (List.range 11).all (fun n =>
    (List.range 11).all (fun m =>
      n == 0 || m == 0 || decide (n < m → primeFib n < primeFib m))) = true := by
  native_decide

example : (List.range 11).all (fun n =>
    n == 0 || (
      decide ((primeFib n).Prime) &&
      orderExec n (primeFib n) &&
      decide (2 ≤ primeFib n))) = true := by
  native_decide

-- `fib_result_prop`, `nth_result_prop` and `order_result_prop` quantify over
-- indices. Their executable counterparts are `orderExec` (checked above) together
-- with the ground equalities in the unit tests. `isPrime_correct_prop` is
-- decidable, so it is sampled directly.

example : (List.range 200).all (fun p => isPrime p == decide (p.Prime)) = true := by
  native_decide

#eval Plausible.Testable.check (∀ p : Nat, isPrime p = decide (p.Prime))

#eval Plausible.Testable.check
  (∀ n : Fin 10, (primeFib (n.val + 1)).Prime)

#eval Plausible.Testable.check
  (∀ n : Fin 10, 2 ≤ primeFib (n.val + 1))

#eval Plausible.Testable.check
  (∀ n : Fin 9, primeFib (n.val + 1) < primeFib (n.val + 2))

#eval Plausible.Testable.check
  (∀ n : Fin 10, orderExec (n.val + 1) (primeFib (n.val + 1)) = true)

/-! ## Correctness -/

theorem correctness_thm {n : Nat} (hn : Pre n) : Post_prop n :=
  ⟨prime_result_thm hn, fib_result_thm hn, nth_result_thm hn,
    order_result_thm hn, ge_two_thm hn⟩

/-! ## Imperative implementation -/

/-- Mutable loop state: Fibonacci pair, primes still needed, whether the
answer has already been found, and that answer. -/
structure LoopState where
  prev : Nat
  curr : Nat
  remaining : Nat
  found : Bool
  result : Nat
deriving DecidableEq, Repr

/-- Body of the Python `while` loop. Once a value has been returned the
state is frozen, which is the mutable counterpart of an early `return`. -/
def impStep (st : LoopState) : LoopState :=
  if st.found then
    st
  else
    let next := st.prev + st.curr
    let remaining' := if isPrime next then st.remaining - 1 else st.remaining
    if remaining' = 0 then
      { prev := st.curr, curr := next, remaining := remaining', found := true, result := next }
    else
      { prev := st.curr, curr := next, remaining := remaining', found := false, result := 0 }

/-- Run `fuel` imperative steps from `st`. -/
def runSteps (fuel : Nat) (st : LoopState) : LoopState :=
  (List.range fuel).foldl (fun s _ => impStep s) st

/-- Python loop as an `Id` computation with mutable state. -/
def primeFibImp (n : Nat) : Nat :=
  Id.run do
    let mut st : LoopState :=
      { prev := 0, curr := 1, remaining := n, found := false, result := 0 }
    for _ in List.range searchFuel do
      st := impStep st
    return st.result

/-! ## Imperative tests -/

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
example : primeFibImp 0 = 1 := by native_decide

#eval primeFibImp 1
#eval primeFibImp 5
#eval primeFibImp 10

/-! ## Equivalence -/

private theorem runSteps_succ_back (fuel : Nat) (st : LoopState) :
    runSteps (fuel + 1) st = impStep (runSteps fuel st) := by
  simp [runSteps, List.range_succ, List.foldl_append]

private theorem runSteps_succ_front (fuel : Nat) (st : LoopState) :
    runSteps (fuel + 1) st = runSteps fuel (impStep st) := by
  induction fuel generalizing st with
  | zero => simp [runSteps]
  | succ fuel ih =>
    rw [runSteps_succ_back (fuel + 1), ih, runSteps_succ_back]

private theorem impStep_found (st : LoopState) (h : st.found = true) : impStep st = st := by
  simp [impStep, h]

private theorem runSteps_found (fuel : Nat) (st : LoopState) (h : st.found = true) :
    runSteps fuel st = st := by
  induction fuel with
  | zero => simp [runSteps]
  | succ fuel ih =>
    rw [runSteps_succ_front, impStep_found st h, ih]

private def startState (prev curr remaining : Nat) : LoopState where
  prev := prev
  curr := curr
  remaining := remaining
  found := false
  result := 0

private def foundState (prev curr result : Nat) : LoopState where
  prev := prev
  curr := curr
  remaining := 0
  found := true
  result := result

private theorem runSteps_eq_loop :
    ∀ {fuel prev curr remaining : Nat},
      (runSteps fuel (startState prev curr remaining)).result =
        primeFibLoop prev curr remaining fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro prev curr remaining
    simp [runSteps, primeFibLoop, startState]
  | succ fuel ih =>
    intro prev curr remaining
    rw [runSteps_succ_front]
    by_cases hp : isPrime (prev + curr) = true
    · by_cases h0 : remaining - 1 = 0
      · have hstep : impStep (startState prev curr remaining) =
            foundState curr (prev + curr) (prev + curr) := by
          simp [impStep, startState, foundState, hp, h0]
        rw [hstep, runSteps_found fuel _ (by simp [foundState]), primeFibLoop]
        simp [foundState, hp, h0]
      · have hstep : impStep (startState prev curr remaining) =
            startState curr (prev + curr) (remaining - 1) := by
          simp [impStep, startState, hp, h0]
        rw [hstep, primeFibLoop]
        simpa [hp, h0] using
          ih (prev := curr) (curr := prev + curr) (remaining := remaining - 1)
    · by_cases h0 : remaining = 0
      · have hstep : impStep (startState prev curr remaining) =
            foundState curr (prev + curr) (prev + curr) := by
          simp [impStep, startState, foundState, hp, h0]
        rw [hstep, runSteps_found fuel _ (by simp [foundState]), primeFibLoop]
        simp [foundState, hp, h0]
      · have hstep : impStep (startState prev curr remaining) =
            startState curr (prev + curr) remaining := by
          simp [impStep, startState, hp, h0]
        rw [hstep, primeFibLoop]
        simpa [hp, h0] using
          ih (prev := curr) (curr := prev + curr) (remaining := remaining)

private theorem primeFibImp_eq_runSteps (n : Nat) :
    primeFibImp n = (runSteps searchFuel (startState 0 1 n)).result := by
  simp [primeFibImp, runSteps, startState, searchFuel, impStep, List.range_succ,
    List.foldl_cons, List.foldl_nil, Id.run]
  rfl

theorem equivalence_thm (n : Nat) : primeFib n = primeFibImp n := by
  rw [primeFibImp_eq_runSteps, primeFib]
  symm
  exact runSteps_eq_loop (fuel := searchFuel) (prev := 0) (curr := 1) (remaining := n)

-- PBT for functional/imperative equivalence, exhaustive on a bound past the tests.
example : (List.range 16).all (fun n => primeFib n == primeFibImp n) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ n : Fin 16, primeFib n.val = primeFibImp n.val)

end humaneval_39_prime_fib
