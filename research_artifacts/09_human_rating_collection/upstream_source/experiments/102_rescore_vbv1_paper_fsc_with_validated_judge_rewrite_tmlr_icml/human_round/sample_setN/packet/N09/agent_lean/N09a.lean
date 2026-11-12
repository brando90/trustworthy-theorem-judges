import Mathlib

/-!
# HumanEval/39 — `prime_fib`

We formalise the Python program

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

`prime_fib n` returns the `n`-th (1-based) positive integer that is both a
Fibonacci number and prime: `2, 3, 5, 13, 89, 233, 1597, 28657, 514229,
433494437, …`.

## Modelling notes

* `is_prime p` checks that no `k ∈ [2, min(⌊√p⌋ + 1, p - 1))` divides `p`.
  For `p ≥ 4` we have `⌊√p⌋ + 1 ≤ p - 1`, and for `p ∈ {2, 3}` the range is
  empty, so the Python loop is equivalent to checking every `k` with
  `2 ≤ k ≤ ⌊√p⌋`; this is exactly what `isPrime` below does.

* The Python `while True` loop has no a priori termination guarantee (it is
  an open problem whether there are infinitely many Fibonacci primes).  We
  therefore model the search with a fuel parameter; running out of fuel
  yields `0`.  Every theorem about the answer is stated under the hypothesis
  `primeFib n ≠ 0` ("the search found a value"), which matches the Python
  semantics on every input where the Python program terminates.  The fuel of
  1000 iterations is ample for all tested inputs (`n = 10` needs 42 steps).
-/

namespace humaneval_39_prime_fib

/-- The Fibonacci numbers: `0, 1, 1, 2, 3, 5, 8, 13, 21, …`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

/-- Python's `is_prime` as a Boolean test: trial division over `2 ≤ k ≤ √p`. -/
def isPrime (p : Nat) : Bool :=
  if p < 2 then false
  else (List.range' 2 (p.sqrt - 1)).all (fun k => p % k != 0)

/-- `isPrime` decides `Nat.Prime`. -/
theorem isPrime_iff {p : Nat} : isPrime p = true ↔ Nat.Prime p := by
  unfold isPrime
  by_cases hp2 : p < 2
  · rw [if_pos hp2]
    constructor
    · intro h
      exact Bool.noConfusion h
    · intro hP
      have h2 := hP.two_le
      omega
  · rw [if_neg hp2]
    push_neg at hp2
    rw [Nat.prime_def_le_sqrt]
    constructor
    · intro hall
      refine ⟨hp2, ?_⟩
      intro m hm2 hmle hdvd
      have hmem : m ∈ List.range' 2 (p.sqrt - 1) := by
        rw [List.mem_range']
        exact ⟨m - 2, by omega, by omega⟩
      have h0 : (p % m != 0) = true := (List.all_eq_true.mp hall) m hmem
      rw [bne_iff_ne] at h0
      exact h0 (Nat.mod_eq_zero_of_dvd hdvd)
    · intro hP
      rw [List.all_eq_true]
      intro m hm
      show (p % m != 0) = true
      rw [List.mem_range'] at hm
      obtain ⟨i, hilt, hmeq⟩ := hm
      have hm2 : 2 ≤ m := by omega
      have hmsqrt : m ≤ p.sqrt := by omega
      rw [bne_iff_ne]
      intro hmod
      exact hP.2 m hm2 hmsqrt (Nat.dvd_of_mod_eq_zero hmod)

/-- Number of Fibonacci primes among `fib 0, …, fib (i-1)`.  This executable
counter makes "`r` is the `n`-th Fibonacci prime" precise. -/
def primeFibCount (i : Nat) : Nat :=
  ((List.range i).filter fun j => isPrime (fib j)).length

theorem primeFibCount_succ (k : Nat) :
    primeFibCount (k + 1) =
      primeFibCount k + (if isPrime (fib k) then 1 else 0) := by
  unfold primeFibCount
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases h : isPrime (fib k) = true <;> simp [h, List.filter]

theorem primeFibCount_succ2 (i : Nat) :
    primeFibCount (i + 3) =
      primeFibCount (i + 2) + (if isPrime (fib (i + 2)) then 1 else 0) := by
  show primeFibCount (i + 2 + 1) = _
  exact primeFibCount_succ (i + 2)

/-- State of the search loop.  Invariants: `a = fib i` and `b = fib (i+1)` for
some `i`, `m` counts how many Fibonacci primes remain to be found, and `r`
holds the answer (`0` while the loop is still running). -/
structure PFState where
  a : Nat
  b : Nat
  m : Nat
  r : Nat

namespace PFState

/-- Initial state: `(fib 0, fib 1, n, 0)`. -/
def init (n : Nat) : PFState := ⟨0, 1, n, 0⟩

/-- One iteration of the Python loop body: consider the next Fibonacci number
`c = a + b`; if it is prime decrease the counter, and when the counter reaches
`0` record `c` as the answer. -/
def step (s : PFState) : PFState :=
  if isPrime (s.a + s.b) then
    if s.m = 1 then ⟨s.b, s.a + s.b, s.m, s.a + s.b⟩
    else ⟨s.b, s.a + s.b, s.m - 1, 0⟩
  else ⟨s.b, s.a + s.b, s.m, 0⟩

/-- `step`, frozen once the answer has been found. -/
def guardedStep (s : PFState) : PFState :=
  if s.r = 0 then s.step else s

end PFState

/-- Functional loop: at most `fuel` iterations, starting from state `s`. -/
def primeFibAux : Nat → PFState → PFState
  | 0, s => s
  | fuel + 1, s => if s.r = 0 then primeFibAux fuel s.step else s

/-- Functional `prime_fib`. -/
def primeFib (n : Nat) : Nat := (primeFibAux 1000 (PFState.init n)).r

-- ## Unit tests

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

#eval primeFib 5    -- 89
#eval primeFib 10   -- 433494437

-- ## Specification

/-- Pre-condition: `n ≥ 1` (for `n = 0` the Python program never returns,
because `n` is only decremented after the first Fibonacci prime is seen). -/
def Pre (n : Nat) : Prop := 1 ≤ n

/-- Property 1: the answer is prime. -/
def prime_prop (r : Nat) : Prop := Nat.Prime r

/-- Property 2: the answer is a Fibonacci number. -/
def isFib_prop (r : Nat) : Prop := ∃ i : Nat, fib i = r

/-- Property 3: the answer is the `n`-th (1-based) Fibonacci prime, i.e. some
Fibonacci number `fib i` with exactly `n - 1` Fibonacci primes before it. -/
def nth_prop (n r : Nat) : Prop := ∃ i : Nat, fib i = r ∧ primeFibCount i = n - 1

/-- Post-condition: conjunction of the three properties. -/
def Post_prop (n r : Nat) : Prop :=
  prime_prop r ∧ isFib_prop r ∧ nth_prop n r

-- ## Correctness proof

theorem primeFibAux_eq_of_r_ne_zero (fuel : Nat) (s : PFState) (h : s.r ≠ 0) :
    primeFibAux fuel s = s := by
  cases fuel with
  | zero => rfl
  | succ f =>
    simp only [primeFibAux]
    rw [if_neg h]

/-- Key lemma: the loop satisfies its specification.  If the state has
invariants `a = fib i`, `b = fib (i+1)` and `m ≥ 1`, and the run finds an
answer, then the answer is the `(c + m)`-th Fibonacci prime, where
`c = primeFibCount (i+2)` is the number of Fibonacci primes already examined. -/
theorem primeFibAux_spec (fuel : Nat) :
    ∀ (s : PFState) (i : Nat),
      s.a = fib i → s.b = fib (i + 1) → 1 ≤ s.m → s.r = 0 →
        (primeFibAux fuel s).r ≠ 0 →
          Post_prop (primeFibCount (i + 2) + s.m) (primeFibAux fuel s).r := by
  induction fuel with
  | zero =>
    intro s i ha hb hm hs h
    exact absurd hs h
  | succ fuel ih =>
    intro s i ha hb hm hs h
    have hstep : primeFibAux (fuel + 1) s = primeFibAux fuel s.step := by
      simp only [primeFibAux]
      rw [if_pos hs]
    rw [hstep] at h ⊢
    have hcfib : s.a + s.b = fib (i + 2) := by
      rw [ha, hb]
      simp only [fib]
      exact Nat.add_comm _ _
    by_cases hp : isPrime (s.a + s.b) = true
    · by_cases hm1 : s.m = 1
      · -- the searched prime is found now
        have hstepeq : s.step = ⟨s.b, s.a + s.b, s.m, s.a + s.b⟩ := by
          simp [PFState.step, hp, hm1]
        have hcne : s.a + s.b ≠ 0 := by
          have hP := isPrime_iff.mp hp
          have hpos := hP.pos
          omega
        have hres : primeFibAux fuel s.step = s.step :=
          primeFibAux_eq_of_r_ne_zero fuel s.step (by rw [hstepeq]; exact hcne)
        rw [hres, hstepeq]
        show Post_prop (primeFibCount (i + 2) + s.m) (s.a + s.b)
        rw [hm1]
        refine ⟨isPrime_iff.mp hp, ⟨i + 2, hcfib.symm⟩, i + 2, hcfib.symm, ?_⟩
        rw [Nat.add_sub_cancel]
      · -- a prime, but more primes remain
        have hstepeq : s.step = ⟨s.b, s.a + s.b, s.m - 1, 0⟩ := by
          simp [PFState.step, hp, hm1]
        have hm' : 1 ≤ s.m - 1 := by omega
        have ih' := ih s.step (i + 1) (by rw [hstepeq]; exact hb)
          (by rw [hstepeq]; exact hcfib) (by rw [hstepeq]; exact hm') (by simp [hstepeq]) h
        have hcount : primeFibCount (i + 1 + 2) = primeFibCount (i + 2) + 1 := by
          have h2 := primeFibCount_succ2 i
          rw [← hcfib] at h2
          rw [if_pos hp] at h2
          exact h2
        have harg : primeFibCount (i + 1 + 2) + s.step.m =
            primeFibCount (i + 2) + s.m := by
          rw [hstepeq, hcount]
          show primeFibCount (i + 2) + 1 + (s.m - 1) = primeFibCount (i + 2) + s.m
          omega
        rwa [harg] at ih'
    · have hp' : isPrime (s.a + s.b) = false := by
        cases h1 : isPrime (s.a + s.b) with
        | false => rfl
        | true => exact absurd h1 hp
      have hstepeq : s.step = ⟨s.b, s.a + s.b, s.m, 0⟩ := by
        simp [PFState.step, hp']
      have ih' := ih s.step (i + 1) (by rw [hstepeq]; exact hb)
        (by rw [hstepeq]; exact hcfib) (by rw [hstepeq]; exact hm) (by simp [hstepeq]) h
      have hcount : primeFibCount (i + 1 + 2) = primeFibCount (i + 2) := by
        have h2 := primeFibCount_succ2 i
        rw [← hcfib] at h2
        rw [if_neg hp] at h2
        simpa using h2
      have harg : primeFibCount (i + 1 + 2) + s.step.m =
          primeFibCount (i + 2) + s.m := by
        rw [hstepeq, hcount]
      rwa [harg] at ih'

/-- The functional implementation meets its specification: on any admissible
input for which the search terminates, the answer is the `n`-th Fibonacci
prime. -/
theorem primeFib_spec (n : Nat) (hn : Pre n) (hterm : primeFib n ≠ 0) :
    Post_prop n (primeFib n) := by
  have h := primeFibAux_spec 1000 (PFState.init n) 0 rfl rfl hn rfl hterm
  have h0 : primeFibCount (0 + 2) = 0 := rfl
  rw [h0, Nat.zero_add] at h
  exact h

theorem prime_prop_thm (n : Nat) (hn : Pre n) (hterm : primeFib n ≠ 0) :
    prime_prop (primeFib n) :=
  (primeFib_spec n hn hterm).1

theorem isFib_prop_thm (n : Nat) (hn : Pre n) (hterm : primeFib n ≠ 0) :
    isFib_prop (primeFib n) :=
  (primeFib_spec n hn hterm).2.1

theorem nth_prop_thm (n : Nat) (hn : Pre n) (hterm : primeFib n ≠ 0) :
    nth_prop n (primeFib n) :=
  (primeFib_spec n hn hterm).2.2

-- ## Property-based tests

-- PBT for `prime_prop` (randomised, executable form `isPrime` of the property)
#eval Plausible.Testable.check (∀ n : Nat, 1 ≤ n → n ≤ 10 → isPrime (primeFib n) = true)

-- Bounded PBT for `prime_prop`
example : (List.range' 1 10).all (fun n => isPrime (primeFib n)) = true := by
  native_decide

/-- The first 13 Fibonacci numbers (enough to cover `primeFib n` for
`n ≤ 5`, since `primeFib 5 = 89 = fib 11`). -/
def fibs13 : List Nat := (List.range 13).map fib

/-- The Fibonacci primes among the first 13 Fibonacci numbers:
`[2, 3, 5, 13, 89]`. -/
def primeFibs13 : List Nat := fibs13.filter isPrime

/-- Executable form of `isFib_prop` at `n` (for `n ≤ 5`). -/
def isFibOf (n : Nat) : Bool := fibs13.contains (primeFib n)

/-- Executable form of `nth_prop` at `n` (for `n ≤ 5`): `primeFib n` is the
`(n-1)`-th (0-based) Fibonacci prime among the first 13 Fibonacci numbers,
which means exactly `n - 1` Fibonacci primes occur before it. -/
def nthOf (n : Nat) : Bool := primeFibs13[n - 1]? == some (primeFib n)

/-- Executable form of `Post_prop` at `n` (for `n ≤ 5`): this single lookup
entails all three conjuncts (being the `(n-1)`-th Fibonacci prime means being
prime, being a Fibonacci number, and having exactly `n - 1` Fibonacci primes
before it). -/
def postOf (n : Nat) : Bool := nthOf n

-- Bounded PBT for `isFib_prop` (kernel-checked exhaustive small cases)
example : (List.range' 1 5).all (fun n => isFibOf n) = true := by decide

-- Bounded PBT for `nth_prop` (kernel-checked exhaustive small cases)
example : (List.range' 1 5).all (fun n => nthOf n) = true := by decide

-- Bounded PBT for `Post_prop` (kernel-checked exhaustive small cases)
example : (List.range' 1 5).all (fun n => postOf n) = true := by decide

-- ## Correctness theorem: `Pre → Post`

theorem primeFib_correct (n : Nat) (hn : Pre n) (hterm : primeFib n ≠ 0) :
    Post_prop n (primeFib n) :=
  primeFib_spec n hn hterm

-- ## Imperative implementation

/-- Imperative `prime_fib`: the same loop, written with `Id.run` and a mutable
state variable. -/
def primeFibImp (n : Nat) : Nat := Id.run do
  let mut s : PFState := PFState.init n
  for _ in List.range 1000 do
    s := PFState.guardedStep s
  return s.r

-- ## Imperative tests

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

#eval primeFibImp 5    -- 89
#eval primeFibImp 10   -- 433494437

-- ## Equivalence of the two implementations

/-- A `for` loop whose body always yields is just a fold. -/
theorem forIn_yield_eq_foldl {α : Type} (f : PFState → PFState) :
    ∀ (xs : List α) (s : PFState),
      (forIn (m := Id) xs s (fun _ s => pure (ForInStep.yield (f s)))) =
        xs.foldl (fun s _ => f s) s := by
  intro xs
  induction xs with
  | nil => intro s; rfl
  | cons x xs ih =>
    intro s
    rw [List.forIn_cons]
    show forIn (m := Id) xs (f s)
        (fun (_ : α) (s : PFState) => (pure (ForInStep.yield (f s)) : Id (ForInStep PFState)))
       = List.foldl (fun s _ => f s) (f s) xs
    rw [ih]

theorem iterate_apply_last {α : Type} (f : α → α) (k : Nat) (s : α) :
    f (Nat.iterate f k s) = Nat.iterate f (k + 1) s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    show f (Nat.iterate f k (f s)) = Nat.iterate f (k + 1) (f s)
    exact ih (f s)

theorem foldl_range_eq_iterate (f : PFState → PFState) :
    ∀ (k : Nat) (s : PFState),
      (List.range k).foldl (fun s _ => f s) s = Nat.iterate f k s := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    exact iterate_apply_last f k s

theorem iterate_guardedStep_eq_primeFibAux :
    ∀ (k : Nat) (s : PFState),
      Nat.iterate PFState.guardedStep k s = primeFibAux k s := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    show Nat.iterate PFState.guardedStep k (PFState.guardedStep s) = primeFibAux (k + 1) s
    rw [ih]
    by_cases h : s.r = 0
    · have hgs : PFState.guardedStep s = s.step := by simp [PFState.guardedStep, h]
      rw [hgs]
      simp only [primeFibAux]
      rw [if_pos h]
    · have hgs : PFState.guardedStep s = s := by simp [PFState.guardedStep, h]
      rw [hgs]
      simp only [primeFibAux]
      rw [if_neg h]
      exact primeFibAux_eq_of_r_ne_zero k s h

/-- The imperative and functional implementations agree on every input. -/
theorem primeFib_imp_equiv (n : Nat) : primeFibImp n = primeFib n := by
  show ((forIn (m := Id) (List.range 1000) (PFState.init n)
    (fun (_ : Nat) (s : PFState) =>
      (pure (ForInStep.yield (PFState.guardedStep s)) : Id (ForInStep PFState)))).r)
    = primeFib n
  rw [forIn_yield_eq_foldl, foldl_range_eq_iterate, iterate_guardedStep_eq_primeFibAux]
  rfl

end humaneval_39_prime_fib