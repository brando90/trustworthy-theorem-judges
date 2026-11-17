import Mathlib

/-!
# HumanEval/39 — `prime_fib`

Lean 4 formalization of the Python program `humaneval_39_prime_fib.py`.

`prime_fib n` returns the `n`-th number (1-indexed) that is both a Fibonacci number and a
prime.  The Python program generates the Fibonacci sequence `f = [0, 1, 1, 2, 3, 5, ...]`
in a `while True` loop, decrements `n` every time the freshly appended value is prime
(checked by trial division) and returns the current value as soon as `n` reaches `0`.

## Modelling choices

* The Python loop has no a-priori bound: it stops only after the `n`-th prime Fibonacci
  number has been produced (whether infinitely many exist is an open problem).  The
  functional model therefore takes an explicit `fuel : Nat`, the maximal number of loop
  iterations, and returns `Option Nat`: `some v` when the loop returned `v` within `fuel`
  iterations and `none` when the fuel ran out (Python would simply keep running).
  More fuel never changes a `some` result (`fuel_mono_thm`) and a result is produced
  exactly when the fuel covers the answer (`complete_thm`).
* `n` is modelled as a `Nat`.  The Python contract (`Pre`) is `1 ≤ n`; the quirky behaviour
  of the Python code for `n = 0` (it returns `1`) is reproduced faithfully
  (`primeFib_zero`), negative `n` (Python loops forever) is outside the domain.
* `int(math.sqrt(p))` is modelled by the exact integer square root `Nat.sqrt`.
-/

namespace humaneval_39_prime_fib

/-! ## Functional implementation -/

/-- Python's inner `is_prime`: trial division by every `k` in
`range(2, min(int(sqrt p) + 1, p - 1))`. -/
def isPrime (p : Nat) : Bool :=
  if p < 2 then false
  else
    let stop := min (Nat.sqrt p + 1) (p - 1)
    (List.range' 2 (stop - 2)).all (fun k => p % k != 0)

/-- The `while True` loop of the Python program: `a, b` are the last two Fibonacci numbers
(`f[-2], f[-1]`), `n` the remaining count and `fuel` the number of iterations still allowed. -/
def primeFibAux : (fuel n a b : Nat) → Option Nat
  | 0, _, _, _ => none
  | fuel + 1, n, a, b =>
    let c := a + b
    let n' := if isPrime c then n - 1 else n
    if n' = 0 then some c else primeFibAux fuel n' b c

/-- `prime_fib n`: the `n`-th prime Fibonacci number, searched for with at most `fuel` loop
iterations (the loop starts from `f = [0, 1]`, i.e. `a = fib 0`, `b = fib 1`). -/
def primeFib (n : Nat) (fuel : Nat := 100) : Option Nat :=
  primeFibAux fuel n 0 1

/-! ## Unit tests (the `check` function of the Python file) -/

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
-- Python quirk: `prime_fib(0)` returns `1` (the first appended value `f[-1] = 1`).
example : primeFib 0 = some 1 := by native_decide
-- Not enough fuel: `prime_fib(5)` needs `fib 11 = 89`, i.e. 10 loop iterations.
example : primeFib 5 9 = none := by native_decide
example : primeFib 5 10 = some 89 := by native_decide

#eval primeFib 1
#eval primeFib 10
#eval (List.range 11).map fun n => primeFib n
#eval primeFib 5 3   -- not enough fuel
#eval (List.range 50).filter isPrime

/-! ## Specification vocabulary -/

/-- `PrimeFibIdx j`: the `j`-th Fibonacci number is prime. -/
abbrev PrimeFibIdx (j : Nat) : Prop := Nat.Prime (Nat.fib j)

/-- `IsFib m`: `m` is a Fibonacci number. -/
def IsFib (m : Nat) : Prop := ∃ j, Nat.fib j = m

/-- `PrimeFibNum m`: `m` is a prime Fibonacci number. -/
def PrimeFibNum (m : Nat) : Prop := Nat.Prime m ∧ IsFib m

theorem le_fib_add_one (j : Nat) : j ≤ Nat.fib j + 1 := by
  rcases le_or_gt 5 j with h | h
  · exact (Nat.le_fib_self h).trans (Nat.le_succ _)
  · interval_cases j <;> decide

theorem exists_le_fib (m : Nat) : ∃ j, m ≤ Nat.fib j :=
  ⟨m + 1, by have := le_fib_add_one (m + 1); omega⟩

/-- Index of the first Fibonacci number `≥ m` (a cheap way to decide `IsFib`). -/
def fibIndexGE (m : Nat) : Nat := Nat.find (exists_le_fib m)

theorem isFib_iff_fibIndexGE (m : Nat) : IsFib m ↔ Nat.fib (fibIndexGE m) = m := by
  constructor
  · rintro ⟨j, rfl⟩
    have h1 : fibIndexGE (Nat.fib j) ≤ j := Nat.find_min' _ le_rfl
    have h2 : Nat.fib j ≤ Nat.fib (fibIndexGE (Nat.fib j)) := Nat.find_spec (exists_le_fib _)
    exact le_antisymm (Nat.fib_mono h1) h2
  · intro h
    exact ⟨_, h⟩

instance : DecidablePred IsFib := fun m =>
  decidable_of_iff _ (isFib_iff_fibIndexGE m).symm

instance : DecidablePred PrimeFibNum := fun m =>
  inferInstanceAs (Decidable (Nat.Prime m ∧ IsFib m))

/-! ## Basic lemmas -/

/-- Python's `is_prime` is a correct primality test. -/
theorem isPrime_iff (p : Nat) : isPrime p = true ↔ Nat.Prime p := by
  unfold isPrime
  by_cases hp : p < 2
  · simp only [hp, if_true, Bool.false_eq_true, false_iff]
    intro h
    exact absurd h.two_le (by omega)
  · simp only [hp, if_false, List.all_eq_true, List.mem_range'_1, bne_iff_ne, ne_eq]
    rw [Nat.prime_def_le_sqrt]
    constructor
    · intro h
      refine ⟨by omega, fun m hm2 hms hdvd => ?_⟩
      have hmm : m * m ≤ p := Nat.le_sqrt.mp hms
      have hm : m < min (Nat.sqrt p + 1) (p - 1) := by
        have : m + 2 ≤ m * m := by nlinarith
        omega
      exact h m ⟨hm2, by omega⟩ (Nat.mod_eq_zero_of_dvd hdvd)
    · rintro ⟨-, h⟩ m ⟨hm2, hm⟩ hmod
      have hms : m ≤ Nat.sqrt p := by omega
      exact h m hm2 hms (Nat.dvd_of_mod_eq_zero hmod)

theorem PrimeFibIdx.three_le {k : Nat} (h : PrimeFibIdx k) : 3 ≤ k := by
  by_contra hlt
  push_neg at hlt
  interval_cases k
  · exact Nat.not_prime_zero h
  · exact Nat.not_prime_one h
  · exact Nat.not_prime_one h

theorem count_primeFibIdx_two : Nat.count PrimeFibIdx 2 = 0 := by
  simp [Nat.count_succ, PrimeFibIdx, Nat.not_prime_zero, Nat.not_prime_one]

/-- Loop invariant / exact characterisation of the loop started at state
`(a, b) = (fib i, fib (i+1))` with remaining count `m + 1`: it returns `some v` iff `v = fib k`
for the first index `k ≥ i + 2` reachable with the fuel such that `fib k` is prime and exactly
`m` further prime Fibonacci indices lie in `[i + 2, k)`. -/
theorem primeFibAux_spec (fuel : Nat) : ∀ (i m v : Nat),
    primeFibAux fuel (m + 1) (Nat.fib i) (Nat.fib (i + 1)) = some v ↔
      ∃ k, i + 2 ≤ k ∧ k ≤ i + fuel + 1 ∧ PrimeFibIdx k ∧
        Nat.count PrimeFibIdx k = Nat.count PrimeFibIdx (i + 2) + m ∧ v = Nat.fib k := by
  induction fuel with
  | zero =>
    intro i m v
    simp only [primeFibAux, reduceCtorEq, false_iff]
    rintro ⟨k, hk1, hk2, -⟩
    omega
  | succ fuel ih =>
    intro i m v
    have hc : Nat.fib i + Nat.fib (i + 1) = Nat.fib (i + 2) := Nat.fib_add_two.symm
    have ih' : ∀ m, primeFibAux fuel (m + 1) (Nat.fib (i + 1)) (Nat.fib (i + 2)) = some v ↔
        ∃ k, i + 3 ≤ k ∧ k ≤ i + 1 + fuel + 1 ∧ PrimeFibIdx k ∧
          Nat.count PrimeFibIdx k = Nat.count PrimeFibIdx (i + 3) + m ∧ v = Nat.fib k :=
      fun m => ih (i + 1) m v
    simp only [primeFibAux, hc]
    by_cases hp : isPrime (Nat.fib (i + 2)) = true
    · have hP : PrimeFibIdx (i + 2) := (isPrime_iff _).mp hp
      have hcount : Nat.count PrimeFibIdx (i + 3) = Nat.count PrimeFibIdx (i + 2) + 1 := by
        rw [Nat.count_succ, if_pos hP]
      simp only [hp, if_true, Nat.add_sub_cancel]
      cases m with
      | zero =>
        simp only [if_true, Option.some.injEq, Nat.add_zero]
        constructor
        · rintro rfl
          exact ⟨i + 2, le_refl _, by omega, hP, rfl, rfl⟩
        · rintro ⟨k, hk1, hk2, hPk, hcnt, rfl⟩
          rcases Nat.eq_or_lt_of_le hk1 with h | h
          · rw [h]
          · have := Nat.count_monotone PrimeFibIdx (show i + 3 ≤ k by omega)
            omega
      | succ m =>
        simp only [Nat.succ_ne_zero, if_false]
        rw [ih' m]
        constructor
        · rintro ⟨k, hk1, hk2, hPk, hcnt, rfl⟩
          exact ⟨k, by omega, by omega, hPk, by omega, rfl⟩
        · rintro ⟨k, hk1, hk2, hPk, hcnt, rfl⟩
          refine ⟨k, ?_, by omega, hPk, by omega, rfl⟩
          rcases Nat.eq_or_lt_of_le hk1 with h | h
          · subst h; omega
          · omega
    · have hP : ¬ PrimeFibIdx (i + 2) := fun h => hp ((isPrime_iff _).mpr h)
      have hcount : Nat.count PrimeFibIdx (i + 3) = Nat.count PrimeFibIdx (i + 2) := by
        rw [Nat.count_succ, if_neg hP, Nat.add_zero]
      simp only [hp, Bool.false_eq_true, if_false, Nat.succ_ne_zero]
      rw [ih' m]
      constructor
      · rintro ⟨k, hk1, hk2, hPk, hcnt, rfl⟩
        exact ⟨k, by omega, by omega, hPk, by omega, rfl⟩
      · rintro ⟨k, hk1, hk2, hPk, hcnt, rfl⟩
        refine ⟨k, ?_, by omega, hPk, by omega, rfl⟩
        rcases Nat.eq_or_lt_of_le hk1 with h | h
        · subst h; exact absurd hPk hP
        · omega

/-- Exact characterisation of `primeFib` for `1 ≤ n`: it returns `some v` iff `v = fib k`
where `k` is the index of the `n`-th prime Fibonacci number (`fib k` is prime and exactly
`n - 1` smaller indices have a prime Fibonacci number) and the fuel reaches index `k`. -/
theorem primeFib_spec (n fuel v : Nat) (hn : 1 ≤ n) :
    primeFib n fuel = some v ↔
      ∃ k, k ≤ fuel + 1 ∧ PrimeFibIdx k ∧ Nat.count PrimeFibIdx k = n - 1 ∧ v = Nat.fib k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold primeFib
  have h := primeFibAux_spec fuel 0 m v
  simp only [Nat.fib_zero, Nat.fib_one, Nat.zero_add, count_primeFibIdx_two,
    Nat.add_sub_cancel] at h ⊢
  rw [h]
  constructor
  · rintro ⟨k, -, hk2, hPk, hcnt, rfl⟩
    exact ⟨k, hk2, hPk, hcnt, rfl⟩
  · rintro ⟨k, hk2, hPk, hcnt, rfl⟩
    exact ⟨k, by have := hPk.three_le; omega, hk2, hPk, hcnt, rfl⟩

/-- The Python quirk: `prime_fib(0)` returns `1` (after a single loop iteration). -/
theorem primeFib_zero (fuel : Nat) : primeFib 0 (fuel + 1) = some 1 := by
  simp [primeFib, primeFibAux, isPrime]

theorem primeFib_fuel_zero (n : Nat) : primeFib n 0 = none := rfl

/-- Strict monotonicity of `fib` on indices `≥ 2` in the form used below. -/
theorem fib_injOn_three_le {j k : Nat} (hj : 3 ≤ j) (hk : 3 ≤ k)
    (h : Nat.fib j = Nat.fib k) : j = k := by
  rcases lt_trichotomy j k with hlt | heq | hgt
  · have := (Nat.fib_lt_fib (by omega : 2 ≤ j)).mpr hlt
    omega
  · exact heq
  · have := (Nat.fib_lt_fib (by omega : 2 ≤ k)).mpr hgt
    omega

/-- Counting prime Fibonacci *numbers* below `fib k` is the same as counting prime
Fibonacci *indices* below `k`. -/
theorem count_primeFibNum_fib (k : Nat) :
    Nat.count PrimeFibNum (Nat.fib k) = Nat.count PrimeFibIdx k := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  symm
  apply Finset.card_bij (fun j _ => Nat.fib j)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    obtain ⟨hjk, hPj⟩ := hj
    have h3 : 3 ≤ j := hPj.three_le
    exact ⟨(Nat.fib_lt_fib (by omega : 2 ≤ j)).mpr hjk, hPj, j, rfl⟩
  · intro j1 hj1 j2 hj2 heq
    simp only [Finset.mem_filter, Finset.mem_range] at hj1 hj2
    exact fib_injOn_three_le hj1.2.three_le hj2.2.three_le heq
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    obtain ⟨hmk, hpm, j, rfl⟩ := hm
    refine ⟨j, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hpm⟩
    by_contra hjk
    push_neg at hjk
    exact absurd hmk (not_lt.mpr (Nat.fib_mono hjk))

/-! ## Pre-condition -/

/-- Python contract: `n` is a positive count (`prime_fib(n)` for `n ≤ 0` is meaningless;
`n < 0` even loops forever). -/
def Pre (n : Nat) : Prop := 1 ≤ n

/-! ## Properties -/

/-- Any returned value is prime. -/
def prime_prop (r : Option Nat) : Prop := ∀ v, r = some v → Nat.Prime v

theorem prime_thm (n fuel : Nat) (h : Pre n) : prime_prop (primeFib n fuel) := by
  intro v hv
  obtain ⟨k, -, hPk, -, rfl⟩ := (primeFib_spec n fuel v h).mp hv
  exact hPk

/-- Any returned value is a Fibonacci number (this even holds for `n = 0`). -/
def fibonacci_prop (r : Option Nat) : Prop := ∀ v, r = some v → IsFib v

theorem fibonacci_thm (n fuel : Nat) : fibonacci_prop (primeFib n fuel) := by
  intro v hv
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · cases fuel with
    | zero => simp [primeFib_fuel_zero] at hv
    | succ fuel =>
      rw [primeFib_zero] at hv
      exact ⟨1, by simpa using hv⟩
  · obtain ⟨k, -, -, -, rfl⟩ := (primeFib_spec n fuel v hn).mp hv
    exact ⟨k, rfl⟩

/-- Index form of "`n`-th": a returned value is `fib k` where `fib k` is prime and exactly
`n - 1` indices below `k` carry a prime Fibonacci number. -/
def nth_index_prop (n : Nat) (r : Option Nat) : Prop :=
  ∀ v, r = some v → ∃ k, Nat.fib k = v ∧ PrimeFibIdx k ∧ Nat.count PrimeFibIdx k = n - 1

theorem nth_index_thm (n fuel : Nat) (h : Pre n) : nth_index_prop n (primeFib n fuel) := by
  intro v hv
  obtain ⟨k, -, hPk, hcnt, rfl⟩ := (primeFib_spec n fuel v h).mp hv
  exact ⟨k, rfl, hPk, hcnt⟩

/-- Value form of "`n`-th": a returned value `v` is a prime Fibonacci number and exactly
`n - 1` prime Fibonacci numbers are smaller than `v`. -/
def rank_prop (n : Nat) (r : Option Nat) : Prop :=
  ∀ v, r = some v → PrimeFibNum v ∧ Nat.count PrimeFibNum v = n - 1

theorem rank_thm (n fuel : Nat) (h : Pre n) : rank_prop n (primeFib n fuel) := by
  intro v hv
  obtain ⟨k, -, hPk, hcnt, rfl⟩ := (primeFib_spec n fuel v h).mp hv
  exact ⟨⟨hPk, k, rfl⟩, by rw [count_primeFibNum_fib, hcnt]⟩

/-- The returned value is *the* `n`-th prime Fibonacci number (`Nat.nth`, 0-indexed). -/
def nth_prop (n : Nat) (r : Option Nat) : Prop :=
  ∀ v, r = some v → v = Nat.nth PrimeFibNum (n - 1)

theorem nth_thm (n fuel : Nat) (h : Pre n) : nth_prop n (primeFib n fuel) := by
  intro v hv
  obtain ⟨hPv, hcnt⟩ := rank_thm n fuel h v hv
  rw [← hcnt, Nat.nth_count hPv]

/-- The search succeeds exactly when the fuel reaches the answer: the loop with `fuel`
iterations inspects `fib 2, …, fib (fuel + 1)`, so it returns a value iff at least `n` of the
indices `< fuel + 2` carry a prime Fibonacci number. -/
def complete_prop (n fuel : Nat) (r : Option Nat) : Prop :=
  r.isSome = true ↔ n ≤ Nat.count PrimeFibIdx (fuel + 2)

theorem complete_thm (n fuel : Nat) (h : Pre n) : complete_prop n fuel (primeFib n fuel) := by
  unfold complete_prop
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨k, hk, hPk, hcnt, rfl⟩ := (primeFib_spec n fuel v h).mp hv
    have h1 : Nat.count PrimeFibIdx (k + 1) = Nat.count PrimeFibIdx k + 1 := by
      rw [Nat.count_succ, if_pos hPk]
    have h2 := Nat.count_monotone PrimeFibIdx (show k + 1 ≤ fuel + 2 by omega)
    omega
  · intro hle
    have hn : 1 ≤ n := h
    have hlt : n - 1 < Nat.count PrimeFibIdx (fuel + 2) := by omega
    have hk := Nat.nth_lt_of_lt_count hlt
    have hcard : ∀ hf : (setOf PrimeFibIdx).Finite, n - 1 < hf.toFinset.card :=
      fun hf => lt_of_lt_of_le hlt (Nat.count_le_card hf _)
    have hPk := Nat.nth_mem (n - 1) hcard
    have hcnt := Nat.count_nth hcard
    exact ⟨_, (primeFib_spec n fuel _ h).mpr ⟨Nat.nth PrimeFibIdx (n - 1), by omega, hPk, hcnt, rfl⟩⟩

/-- Fuel is only a bound on the number of iterations: a result found with some fuel is found,
unchanged, with any larger fuel (holds for every `n`, including `0`). -/
def fuel_mono_prop (n fuel : Nat) (r : Option Nat) : Prop :=
  ∀ fuel' v, fuel ≤ fuel' → r = some v → primeFib n fuel' = some v

theorem fuel_mono_thm (n fuel : Nat) : fuel_mono_prop n fuel (primeFib n fuel) := by
  intro fuel' v hle hv
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · cases fuel with
    | zero => simp [primeFib_fuel_zero] at hv
    | succ fuel =>
      obtain ⟨f', rfl⟩ : ∃ f', fuel' = f' + 1 := ⟨fuel' - 1, by omega⟩
      rw [primeFib_zero] at hv ⊢
      exact hv
  · obtain ⟨k, hk, hPk, hcnt, rfl⟩ := (primeFib_spec n fuel _ hn).mp hv
    exact (primeFib_spec n fuel' _ hn).mpr ⟨k, by omega, hPk, hcnt, rfl⟩

/-! ## Post-condition -/

/-- Full post-condition of `prime_fib n` computed with `fuel` iterations, result `r`. -/
def Post_prop (n fuel : Nat) (r : Option Nat) : Prop :=
  prime_prop r ∧ fibonacci_prop r ∧ nth_index_prop n r ∧ rank_prop n r ∧ nth_prop n r ∧
    complete_prop n fuel r ∧ fuel_mono_prop n fuel r

/-! ## Property-based tests

Executable Boolean forms of the properties, checked on many inputs.  Fuel is kept `≤ 46`
(Fibonacci numbers up to `fib 47`) so that trial division stays cheap. -/

/-- Executable form of `prime_prop` (uses Mathlib's independent `Nat.Prime` decision). -/
def checkPrime (n fuel : Nat) : Bool :=
  match primeFib n fuel with
  | some v => decide (Nat.Prime v)
  | none => true

/-- Executable form of `fibonacci_prop`. -/
def checkFibonacci (n fuel : Nat) : Bool :=
  match primeFib n fuel with
  | some v => decide (IsFib v)
  | none => true

/-- Executable form of `nth_index_prop` (the witness index is searched below `fuel + 2`). -/
def checkNthIndex (n fuel : Nat) : Bool :=
  match primeFib n fuel with
  | some v => (List.range (fuel + 2)).any fun k =>
      Nat.fib k == v && decide (PrimeFibIdx k) && Nat.count PrimeFibIdx k == n - 1
  | none => true

/-- Executable form of `rank_prop`. -/
def checkRank (n fuel : Nat) : Bool :=
  match primeFib n fuel with
  | some v => decide (PrimeFibNum v) && Nat.count PrimeFibNum v == n - 1
  | none => true

/-- Executable form of `nth_prop`: `Nat.nth` itself is noncomputable, but for a decidable
predicate `Nat.nth p i = v` iff `p v ∧ Nat.count p v = i` (`Nat.nth_count`), which is
exactly `checkRank`. -/
def checkNth (n fuel : Nat) : Bool := checkRank n fuel

/-- Executable form of `complete_prop`. -/
def checkComplete (n fuel : Nat) : Bool :=
  (primeFib n fuel).isSome == decide (n ≤ Nat.count PrimeFibIdx (fuel + 2))

/-- Executable form of `fuel_mono_prop` (for all `fuel' ∈ [fuel, 46]`). -/
def checkFuelMono (n fuel : Nat) : Bool :=
  match primeFib n fuel with
  | some v => (List.range' fuel (47 - fuel)).all fun fuel' => primeFib n fuel' == some v
  | none => true

/-- Executable form of `Post_prop` (all `Pre`-relevant conjuncts). -/
def checkPost (n fuel : Nat) : Bool :=
  checkPrime n fuel && checkFibonacci n fuel && checkNthIndex n fuel && checkRank n fuel &&
    checkNth n fuel && checkComplete n fuel && checkFuelMono n fuel

-- Randomized PBTs (inputs are reduced into the admissible, cheap range by `%`).
#eval Plausible.Testable.check (∀ n fuel : Nat, checkPrime (n % 11 + 1) (fuel % 47) = true)
#eval Plausible.Testable.check (∀ n fuel : Nat, checkFibonacci (n % 12) (fuel % 47) = true)
#eval Plausible.Testable.check (∀ n fuel : Nat, checkNthIndex (n % 11 + 1) (fuel % 47) = true)
#eval Plausible.Testable.check (∀ n fuel : Nat, checkRank (n % 6 + 1) (fuel % 47) = true)
#eval Plausible.Testable.check (∀ n fuel : Nat, checkNth (n % 6 + 1) (fuel % 47) = true)
#eval Plausible.Testable.check (∀ n fuel : Nat, checkComplete (n % 11 + 1) (fuel % 47) = true)
#eval Plausible.Testable.check (∀ n fuel : Nat, checkFuelMono (n % 12) (fuel % 47) = true)
#eval Plausible.Testable.check (∀ n fuel : Nat, checkPost (n % 6 + 1) (fuel % 47) = true)

-- Exhaustive bounded PBTs.
example : (List.range 12).all (fun n => (List.range 47).all fun fuel =>
    checkPrime (n + 1) fuel && checkFibonacci n fuel && checkNthIndex (n + 1) fuel &&
      checkComplete (n + 1) fuel && checkFuelMono n fuel) = true := by native_decide
-- `checkRank`/`checkNth`/`checkPost` count prime Fibonacci numbers below the result, which is
-- linear in the result, so they are checked for `n ≤ 7` (results up to `fib 17 = 1597`).
example : (List.range 7).all (fun n => (List.range 47).all fun fuel =>
    checkRank (n + 1) fuel && checkNth (n + 1) fuel && checkPost (n + 1) fuel) = true := by
  native_decide
-- The primality test agrees with Mathlib on `0 … 2000`.
example : (List.range 2000).all (fun p => isPrime p == decide (Nat.Prime p)) = true := by
  native_decide
#eval Plausible.Testable.check (∀ p : Nat, isPrime p = decide (Nat.Prime p))

/-! ## Correctness theorem -/

theorem primeFib_correct (n fuel : Nat) (h : Pre n) : Post_prop n fuel (primeFib n fuel) :=
  ⟨prime_thm n fuel h, fibonacci_thm n fuel, nth_index_thm n fuel h, rank_thm n fuel h,
    nth_thm n fuel h, complete_thm n fuel h, fuel_mono_thm n fuel⟩

/-! ## Imperative implementation -/

/-- Imperative transcription of the Python program: mutable `a, b` (the last two entries of
`f`), mutable counter `n`, a `for` loop bounded by `fuel` with an early `return`. -/
def primeFibImp (n : Nat) (fuel : Nat := 100) : Option Nat := Id.run do
  let mut a := 0
  let mut b := 1
  let mut n := n
  for _ in List.range fuel do
    let c := a + b
    a := b
    b := c
    if isPrime c then
      n := n - 1
    if n = 0 then
      return some c
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
example : primeFibImp 5 9 = none := by native_decide

#eval primeFibImp 10
#eval (List.range 11).map fun n => primeFibImp n

-- PBT: functional and imperative versions agree.
example : (List.range 13).all (fun n => (List.range 47).all fun fuel =>
    primeFibImp n fuel == primeFib n fuel) = true := by native_decide
#eval Plausible.Testable.check (∀ n fuel : Nat, primeFibImp (n % 13) (fuel % 47) = primeFib (n % 13) (fuel % 47))

/-! ## Equivalence theorem -/

/-- The `for` loop, run over any list of `fuel` elements from an arbitrary state, computes
`primeFibAux`. -/
theorem primeFibImp_loop (l : List Nat) (a b n : Nat) :
    (Id.run do
      let mut a := a
      let mut b := b
      let mut n := n
      for _ in l do
        let c := a + b
        a := b
        b := c
        if isPrime c then
          n := n - 1
        if n = 0 then
          return some c
      return none) = primeFibAux l.length n a b := by
  induction l generalizing a b n with
  | nil => simp [primeFibAux]
  | cons x xs ih =>
    simp only [List.forIn_cons, List.length_cons, primeFibAux]
    by_cases hp : isPrime (a + b) = true
    · simp only [hp, if_true]
      by_cases hn : n - 1 = 0
      · simp [hn]
      · simp only [hn, if_false]
        simpa [hn] using ih b (a + b) (n - 1)
    · simp only [hp, Bool.false_eq_true, if_false]
      by_cases hn : n = 0
      · simp [hn]
      · simp only [hn, if_false]
        simpa [hn] using ih b (a + b) n

theorem primeFibImp_eq_primeFib (n fuel : Nat) : primeFibImp n fuel = primeFib n fuel := by
  have h := primeFibImp_loop (List.range fuel) 0 1 n
  simp only [List.length_range] at h
  exact h

end humaneval_39_prime_fib
