import Mathlib

/-!
# HumanEval/39: `prime_fib`

Formalization of the Python program `humaneval_39_prime_fib.py`.

`prime_fib n` returns the `n`-th number that is both a Fibonacci number and prime.
This file provides:
- The functional implementation (`is_prime`, `is_fib`, `prime_fib_loop`, `prime_fib`)
- Unit tests covering all Python `check(prime_fib)` assertions
- Precondition (`Pre`), property propositions (`_prop`) and kernel-checked theorems (`_thm`)
- Postcondition (`Post_prop`), property-based tests (Plausible and bounded `native_decide`),
  and the overall correctness theorem (`prime_fib_correct`)
- Imperative implementation (`prime_fib_imp`) using `Id.run do` with mutable state,
  imperative unit tests, and the equivalence theorem (`prime_fib_equiv`)
-/

namespace humaneval_39_prime_fib

/-! ## 4. Implementation (Functional Definition) -/

/-- Executable primality check: returns `true` iff `p` is a prime natural number. -/
def is_prime (p : Nat) : Bool :=
  decide (Nat.Prime p)

/-- Bounded helper checking whether `x` appears among `Nat.fib k, ..., Nat.fib (k + fuel - 1)`. -/
def is_fib_from : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, k, x => (Nat.fib k == x) || is_fib_from fuel (k + 1) x

/-- Executable Fibonacci membership predicate: returns `true` iff `∃ k, Nat.fib k = x`. -/
def is_fib (x : Nat) : Bool :=
  is_fib_from (x + 2) 0 x

/-- Tail-recursive Fibonacci search loop mirroring the Python `while True` loop.
At each step it advances `(a, b) ↦ (b, a + b)`, decrements `rem` when `a + b` is prime,
and returns `a + b` as soon as `rem == 0`. -/
def prime_fib_loop : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 2
  | fuel + 1, a, b, rem =>
    let c := a + b
    let rem' := if is_prime c then rem - 1 else rem
    if rem' == 0 then c
    else prime_fib_loop fuel b c rem'

/-- Default search fuel (45 Fibonacci steps reaches past the 10th prime Fibonacci number
`F_43 = 433494437`). -/
def prime_fib_fuel : Nat := 45

/-- `prime_fib n` returns the `n`-th number that is both a Fibonacci number and prime. -/
def prime_fib (n : Nat) : Nat :=
  if n == 0 then 2
  else prime_fib_loop prime_fib_fuel 0 1 n

/-- List of prime Fibonacci numbers encountered in `steps` iterations starting from
`(Nat.fib k, Nat.fib (k + 1))` (i.e. filtering `[Nat.fib (k + 2), ..., Nat.fib (k + 1 + steps)]`
by `is_prime`). -/
def prime_fib_list_from (k steps : Nat) : List Nat :=
  ((List.range steps).map (fun i => Nat.fib (k + 2 + i))).filter (fun x => is_prime x)

/-- List of prime Fibonacci numbers encountered in the first `steps` iterations from `(0, 1)`. -/
def prime_fib_list (steps : Nat) : List Nat :=
  prime_fib_list_from 0 steps

/-! ## 5. Unit Tests -/

example : prime_fib 1 = 2 := by native_decide
example : prime_fib 2 = 3 := by native_decide
example : prime_fib 3 = 5 := by native_decide
example : prime_fib 4 = 13 := by native_decide
example : prime_fib 5 = 89 := by native_decide
example : prime_fib 6 = 233 := by native_decide
example : prime_fib 7 = 1597 := by native_decide
example : prime_fib 8 = 28657 := by native_decide
example : prime_fib 9 = 514229 := by native_decide
example : prime_fib 10 = 433494437 := by native_decide

#eval prime_fib 1
#eval prime_fib 2
#eval prime_fib 3
#eval prime_fib 4
#eval prime_fib 5
#eval prime_fib 6
#eval prime_fib 7
#eval prime_fib 8
#eval prime_fib 9
#eval prime_fib 10

/-! ## 6. Pre-condition Predicate -/

/-- Precondition for `prime_fib`: `n` is a positive 1-based index (`1 ≤ n`). -/
def Pre (n : Nat) : Prop :=
  1 ≤ n

/-! ## 7. Property Propositions and Theorems -/

/-- `is_prime p = true` iff `Nat.Prime p`. -/
theorem is_prime_iff (p : Nat) : is_prime p = true ↔ Nat.Prime p := by
  simp [is_prime]

/-- Characterization of `is_prime` by trial division up to `Nat.sqrt p`, matching the
Python inner loop `for k in range(2, min(int(math.sqrt(p)) + 1, p - 1))`. -/
theorem is_prime_sqrt_iff (p : Nat) :
    is_prime p = true ↔ 2 ≤ p ∧ ∀ k, 2 ≤ k → k ≤ Nat.sqrt p → ¬(k ∣ p) := by
  rw [is_prime_iff, Nat.prime_def_le_sqrt]

/-- Characterization of `is_fib_from`. -/
theorem is_fib_from_iff (fuel k x : Nat) :
    is_fib_from fuel k x = true ↔ ∃ i < fuel, Nat.fib (k + i) = x := by
  induction fuel generalizing k with
  | zero => simp [is_fib_from]
  | succ fuel ih =>
    simp only [is_fib_from, Bool.or_eq_true, beq_iff_eq, ih]
    constructor
    · rintro (h0 | ⟨i, hi, hfib⟩)
      · exact ⟨0, Nat.succ_pos fuel, by simpa using h0⟩
      · exact ⟨i + 1, Nat.succ_lt_succ hi, by simpa [Nat.add_assoc, Nat.add_comm 1] using hfib⟩
    · rintro ⟨i, hi, hfib⟩
      cases i with
      | zero => left; simpa using hfib
      | succ i =>
        right
        refine ⟨i, Nat.lt_of_succ_lt_succ hi, ?_⟩
        simpa [Nat.add_assoc, Nat.add_comm 1] using hfib

/-- Every index `k` satisfies `k < Nat.fib k + 2`. -/
theorem lt_fib_add_two (k : Nat) : k < Nat.fib k + 2 := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    rcases k with _ | _ | _ | k
    · decide
    · decide
    · decide
    · have h1 := ih (k + 1) (by omega)
      have h2 := ih (k + 2) (by omega)
      have hfib : Nat.fib (k + 1 + 1 + 1) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
      have hpos : 0 < Nat.fib (k + 1) := Nat.fib_pos.mpr (by omega)
      omega

/-- `is_fib x = true` iff `x` is a Fibonacci number (`∃ k, Nat.fib k = x`). -/
theorem is_fib_iff (x : Nat) : is_fib x = true ↔ ∃ k, Nat.fib k = x := by
  unfold is_fib
  rw [is_fib_from_iff]
  constructor
  · rintro ⟨i, _, hi⟩
    exact ⟨i, by simpa using hi⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, lt_fib_add_two k, by simp⟩

/-- Core loop invariant: starting from `(Nat.fib k, Nat.fib (k + 1))` with `0 < rem`,
`prime_fib_loop` always returns a prime Fibonacci number `Nat.fib m` with `3 ≤ m`. -/
theorem prime_fib_loop_prime_and_fib (fuel k rem : Nat) (hrem : 0 < rem) :
    Nat.Prime (prime_fib_loop fuel (Nat.fib k) (Nat.fib (k + 1)) rem) ∧
    ∃ m : Nat, Nat.fib m = prime_fib_loop fuel (Nat.fib k) (Nat.fib (k + 1)) rem ∧ 3 ≤ m := by
  induction fuel generalizing k rem with
  | zero =>
    simp only [prime_fib_loop]
    exact ⟨Nat.prime_two, ⟨3, rfl, by omega⟩⟩
  | succ fuel ih =>
    rw [prime_fib_loop]
    have hfib : Nat.fib k + Nat.fib (k + 1) = Nat.fib (k + 2) := Nat.fib_add_two.symm
    simp only [hfib]
    by_cases hp : is_prime (Nat.fib (k + 2)) = true
    · simp only [hp, ↓reduceIte]
      by_cases hr : ((rem - 1) == 0) = true
      · simp only [hr, ↓reduceIte]
        have hprime : Nat.Prime (Nat.fib (k + 2)) := (is_prime_iff _).mp hp
        have hk3 : 3 ≤ k + 2 := by
          by_contra hlt
          interval_cases (k + 2)
          · exact Nat.not_prime_zero hprime
          · exact Nat.not_prime_one hprime
          · exact Nat.not_prime_one hprime
        exact ⟨hprime, ⟨k + 2, rfl, hk3⟩⟩
      · have hr0 : rem - 1 ≠ 0 := fun h => hr (beq_iff_eq.mpr h)
        have hr_pos : 0 < rem - 1 := Nat.pos_of_ne_zero hr0
        simp only [hr, Bool.false_eq_true, ↓reduceIte]
        exact ih (k + 1) (rem - 1) hr_pos
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      have hr : (rem == 0) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hrem)
      simp only [hr, Bool.false_eq_true, ↓reduceIte]
      exact ih (k + 1) rem hrem

/-- Combined theorem that `prime_fib n` is always a prime Fibonacci number with index `≥ 3`. -/
theorem prime_fib_prime_and_fib (n : Nat) :
    Nat.Prime (prime_fib n) ∧ ∃ m : Nat, Nat.fib m = prime_fib n ∧ 3 ≤ m := by
  unfold prime_fib
  by_cases hn : (n == 0) = true
  · simp only [hn, ↓reduceIte]
    exact ⟨Nat.prime_two, ⟨3, rfl, by omega⟩⟩
  · have hn0 : n ≠ 0 := fun h => hn (beq_iff_eq.mpr h)
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
    simp only [hn, Bool.false_eq_true, ↓reduceIte]
    exact prime_fib_loop_prime_and_fib prime_fib_fuel 0 n hn_pos

/-- Property 1: `prime_fib n` is a prime number. -/
def is_prime_prop (n : Nat) : Prop :=
  Nat.Prime (prime_fib n)

theorem is_prime_thm (n : Nat) (_h : Pre n) : is_prime_prop n :=
  (prime_fib_prime_and_fib n).1

theorem is_prime_bool_thm (n : Nat) (h : Pre n) : is_prime (prime_fib n) = true :=
  (is_prime_iff _).mpr (is_prime_thm n h)

/-- Property 2: `prime_fib n` is a Fibonacci number (`∃ k, Nat.fib k = prime_fib n ∧ 3 ≤ k`). -/
def is_fib_prop (n : Nat) : Prop :=
  ∃ k : Nat, Nat.fib k = prime_fib n ∧ 3 ≤ k

theorem is_fib_thm (n : Nat) (_h : Pre n) : is_fib_prop n :=
  (prime_fib_prime_and_fib n).2

theorem is_fib_bool_thm (n : Nat) (h : Pre n) : is_fib (prime_fib n) = true := by
  rcases is_fib_thm n h with ⟨k, hk, _⟩
  exact (is_fib_iff _).mpr ⟨k, hk⟩

/-- Property 3: `prime_fib n` is at least 2. -/
def ge_two_prop (n : Nat) : Prop :=
  2 ≤ prime_fib n

theorem ge_two_thm (n : Nat) (h : Pre n) : ge_two_prop n :=
  (is_prime_thm n h).two_le

/-- Property 4: `prime_fib n` is strictly positive. -/
def pos_prop (n : Nat) : Prop :=
  0 < prime_fib n

theorem pos_thm (n : Nat) (h : Pre n) : pos_prop n :=
  (is_prime_thm n h).pos

/-- Unfolding lemma for `prime_fib_list_from k (fuel + 1)`. -/
theorem prime_fib_list_from_succ (k fuel : Nat) :
    prime_fib_list_from k (fuel + 1) =
      if is_prime (Nat.fib (k + 2)) then
        Nat.fib (k + 2) :: prime_fib_list_from (k + 1) fuel
      else
        prime_fib_list_from (k + 1) fuel := by
  unfold prime_fib_list_from
  rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.filter_cons]
  have hmap : (fun i => Nat.fib (k + 2 + i)) ∘ Nat.succ = (fun i => Nat.fib (k + 1 + 2 + i)) := by
    funext i
    simp only [Function.comp]
    congr 1
    omega
  simp [hmap]

/-- Exact equivalence between `prime_fib_loop` and list indexing `(prime_fib_list_from k fuel).getD (rem - 1) 2`. -/
theorem prime_fib_loop_eq_getD (fuel k rem : Nat) (hrem : 0 < rem) :
    prime_fib_loop fuel (Nat.fib k) (Nat.fib (k + 1)) rem =
      (prime_fib_list_from k fuel).getD (rem - 1) 2 := by
  induction fuel generalizing k rem with
  | zero =>
    simp [prime_fib_loop, prime_fib_list_from]
  | succ fuel ih =>
    rw [prime_fib_loop, prime_fib_list_from_succ]
    have hfib : Nat.fib k + Nat.fib (k + 1) = Nat.fib (k + 2) := Nat.fib_add_two.symm
    simp only [hfib]
    by_cases hp : is_prime (Nat.fib (k + 2)) = true
    · simp only [hp, ↓reduceIte]
      by_cases hr : ((rem - 1) == 0) = true
      · have hr0 : rem - 1 = 0 := beq_iff_eq.mp hr
        simp [hr0]
      · have hr0 : rem - 1 ≠ 0 := fun h => hr (beq_iff_eq.mpr h)
        have hr_pos : 0 < rem - 1 := Nat.pos_of_ne_zero hr0
        simp only [hr, Bool.false_eq_true, ↓reduceIte]
        rw [ih (k + 1) (rem - 1) hr_pos]
        cases hrem_eq : rem - 1 with
        | zero => contradiction
        | succ m => simp
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      have hr : (rem == 0) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hrem)
      simp only [hr, Bool.false_eq_true, ↓reduceIte]
      exact ih (k + 1) rem hrem

/-- Property 5: `prime_fib n` equals the `(n - 1)`-th element of the filtered list of
prime Fibonacci numbers `prime_fib_list prime_fib_fuel` (with default `2`). -/
def nth_in_list_prop (n : Nat) : Prop :=
  prime_fib n = (prime_fib_list prime_fib_fuel).getD (n - 1) 2

theorem nth_in_list_thm (n : Nat) (h : Pre n) : nth_in_list_prop n := by
  unfold Pre at h
  unfold nth_in_list_prop prime_fib prime_fib_list
  have hn : (n == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  simp only [hn, Bool.false_eq_true, ↓reduceIte]
  exact prime_fib_loop_eq_getD prime_fib_fuel 0 n (by omega)

/-- Length of `prime_fib_list_from k steps` is non-decreasing with `steps`. -/
theorem prime_fib_list_from_length_le_succ (k steps : Nat) :
    (prime_fib_list_from k steps).length ≤ (prime_fib_list_from k (steps + 1)).length := by
  unfold prime_fib_list_from
  rw [List.range_succ, List.map_append, List.filter_append, List.length_append]
  omega

theorem prime_fib_list_from_length_mono (k : Nat) :
    Monotone (fun steps => (prime_fib_list_from k steps).length) :=
  monotone_nat_of_le_succ (prime_fib_list_from_length_le_succ k)

theorem prime_fib_list_from_length_succ_of_prime (k d : Nat)
    (hp : Nat.Prime (Nat.fib (k + 2 + d))) :
    (prime_fib_list_from k (d + 1)).length = (prime_fib_list_from k d).length + 1 := by
  unfold prime_fib_list_from
  rw [List.range_succ, List.map_append, List.filter_append, List.length_append]
  have hpb : is_prime (Nat.fib (k + 2 + d)) = true := by simpa [is_prime] using hp
  simp [hpb]

/-- Uniqueness of the step index `d` at which the `rem`-th prime Fibonacci number is reached. -/
theorem prime_fib_index_unique (k d₁ d₂ : Nat)
    (hp₁ : Nat.Prime (Nat.fib (k + 2 + d₁)))
    (hp₂ : Nat.Prime (Nat.fib (k + 2 + d₂)))
    (hlen : (prime_fib_list_from k (d₁ + 1)).length = (prime_fib_list_from k (d₂ + 1)).length) :
    d₁ = d₂ := by
  rcases lt_trichotomy d₁ d₂ with hlt | rfl | hgt
  · have hle : (prime_fib_list_from k (d₁ + 1)).length ≤ (prime_fib_list_from k d₂).length :=
      prime_fib_list_from_length_mono k hlt
    have hsucc := prime_fib_list_from_length_succ_of_prime k d₂ hp₂
    omega
  · rfl
  · have hle : (prime_fib_list_from k (d₂ + 1)).length ≤ (prime_fib_list_from k d₁).length :=
      prime_fib_list_from_length_mono k hgt
    have hsucc := prime_fib_list_from_length_succ_of_prime k d₁ hp₁
    omega

/-- Exact specification of `prime_fib_loop`: when `rem ≤ (prime_fib_list_from k fuel).length`,
`prime_fib_loop` returns `Nat.fib (k + 2 + d)` where `Nat.fib (k + 2 + d)` is prime and
exactly `rem` prime Fibonacci numbers occur in the first `d + 1` steps. -/
theorem prime_fib_loop_nth_spec (fuel k rem : Nat) (hrem : 0 < rem)
    (hlen : rem ≤ (prime_fib_list_from k fuel).length) :
    ∃ d < fuel,
      prime_fib_loop fuel (Nat.fib k) (Nat.fib (k + 1)) rem = Nat.fib (k + 2 + d) ∧
      Nat.Prime (Nat.fib (k + 2 + d)) ∧
      (prime_fib_list_from k (d + 1)).length = rem := by
  induction fuel generalizing k rem with
  | zero =>
    simp [prime_fib_list_from] at hlen
    omega
  | succ fuel ih =>
    rw [prime_fib_loop]
    rw [prime_fib_list_from_succ] at hlen
    have hfib : Nat.fib k + Nat.fib (k + 1) = Nat.fib (k + 2) := Nat.fib_add_two.symm
    simp only [hfib]
    by_cases hp : is_prime (Nat.fib (k + 2)) = true
    · simp only [hp, ↓reduceIte, List.length_cons] at hlen ⊢
      by_cases hr : ((rem - 1) == 0) = true
      · have hr1 : rem = 1 := by
          have hr0 : rem - 1 = 0 := beq_iff_eq.mp hr
          omega
        refine ⟨0, Nat.succ_pos fuel, ?_, ?_, ?_⟩
        · simp [hr]
        · simpa [is_prime] using hp
        · rw [prime_fib_list_from_succ]
          simp [hp, prime_fib_list_from, hr1]
      · have hr0 : rem - 1 ≠ 0 := fun h => hr (beq_iff_eq.mpr h)
        have hr_pos : 0 < rem - 1 := Nat.pos_of_ne_zero hr0
        have hlen' : rem - 1 ≤ (prime_fib_list_from (k + 1) fuel).length := by omega
        simp only [hr, Bool.false_eq_true, ↓reduceIte]
        rcases ih (k + 1) (rem - 1) hr_pos hlen' with ⟨d, hd_lt, hd_eq, hd_prime, hd_len⟩
        refine ⟨d + 1, Nat.succ_lt_succ hd_lt, ?_, ?_, ?_⟩
        · have hidx : k + 1 + 2 + d = k + 2 + (d + 1) := by omega
          rwa [hidx] at hd_eq
        · have hidx : k + 1 + 2 + d = k + 2 + (d + 1) := by omega
          rwa [hidx] at hd_prime
        · rw [prime_fib_list_from_succ]
          simp only [hp, ↓reduceIte, List.length_cons, hd_len]
          omega
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hlen ⊢
      have hr : (rem == 0) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hrem)
      simp only [hr, Bool.false_eq_true, ↓reduceIte]
      rcases ih (k + 1) rem hrem hlen with ⟨d, hd_lt, hd_eq, hd_prime, hd_len⟩
      refine ⟨d + 1, Nat.succ_lt_succ hd_lt, ?_, ?_, ?_⟩
      · have hidx : k + 1 + 2 + d = k + 2 + (d + 1) := by omega
        rwa [hidx] at hd_eq
      · have hidx : k + 1 + 2 + d = k + 2 + (d + 1) := by omega
        rwa [hidx] at hd_prime
      · rw [prime_fib_list_from_succ]
        simp [hp, hd_len]

/-- The count `(prime_fib_list steps).length` equals the number of Fibonacci indices
`j < steps + 2` for which `Nat.fib j` is prime (since `F_0 = 0` and `F_1 = 1` are not prime). -/
theorem prime_fib_list_zero_length_eq (steps : Nat) :
    (prime_fib_list steps).length =
      ((List.range (steps + 2)).filter (fun j => is_prime (Nat.fib j))).length := by
  unfold prime_fib_list prime_fib_list_from
  rw [List.filter_map, List.length_map]
  rw [show steps + 2 = (steps + 1) + 1 by omega]
  rw [List.range_succ_eq_map, List.filter_cons]
  rw [List.range_succ_eq_map, List.map_cons, List.filter_cons]
  have hp0 : is_prime (Nat.fib 0) = false := by decide
  have hp1 : is_prime (Nat.fib 1) = false := by decide
  simp only [hp0, hp1, Nat.succ_eq_add_one, zero_add, Bool.false_eq_true, ↓reduceIte, List.map_map]
  rw [List.filter_map, List.length_map]
  congr 2
  funext i
  simp only [Function.comp]
  congr 2
  omega

/-- Property 6: Exact `n`-th prime Fibonacci characterization.
When `n` is within the number of prime Fibonacci numbers in the search bound,
`prime_fib n` is `Nat.fib (d + 2)` where `Nat.fib (d + 2)` is prime and the count of
prime Fibonacci numbers up to `Nat.fib (d + 2)` is exactly `n`. -/
def nth_prime_fib_prop (n : Nat) : Prop :=
  n ≤ (prime_fib_list prime_fib_fuel).length →
    ∃ d < prime_fib_fuel,
      prime_fib n = Nat.fib (d + 2) ∧
      Nat.Prime (Nat.fib (d + 2)) ∧
      (prime_fib_list (d + 1)).length = n

theorem nth_prime_fib_thm (n : Nat) (h : Pre n) : nth_prime_fib_prop n := by
  intro hlen
  unfold Pre at h
  unfold prime_fib prime_fib_list at *
  have hn : (n == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  simp only [hn, Bool.false_eq_true, ↓reduceIte]
  rcases prime_fib_loop_nth_spec prime_fib_fuel 0 n (by omega) hlen with ⟨d, hd_lt, hd_eq, hd_prime, hd_len⟩
  refine ⟨d, hd_lt, ?_, ?_, hd_len⟩
  · simpa [Nat.add_comm] using hd_eq
  · simpa [Nat.add_comm] using hd_prime

/-- Property 7: Strict monotonicity of `prime_fib` on indices within the search bound. -/
def strict_mono_prop (m n : Nat) : Prop :=
  Pre m → m < n → n ≤ (prime_fib_list prime_fib_fuel).length → prime_fib m < prime_fib n

theorem strict_mono_thm (m n : Nat) : strict_mono_prop m n := by
  intro hm hmn hlen
  have hmlen : m ≤ (prime_fib_list prime_fib_fuel).length := by omega
  have hn1 : Pre n := by unfold Pre at *; omega
  rcases nth_prime_fib_thm m hm hmlen with ⟨d₁, _, hm_eq, hm_prime, hm_len⟩
  rcases nth_prime_fib_thm n hn1 hlen with ⟨d₂, _, hn_eq, _, hn_len⟩
  have hd_lt : d₁ < d₂ := by
    by_contra hge
    have hle : d₂ + 1 ≤ d₁ + 1 := by omega
    have hmono : (prime_fib_list (d₂ + 1)).length ≤ (prime_fib_list (d₁ + 1)).length :=
      prime_fib_list_from_length_mono 0 hle
    omega
  have hd₁_pos : 1 ≤ d₁ := by
    rcases d₁ with _ | d₁
    · exfalso
      exact Nat.not_prime_one hm_prime
    · omega
  rw [hm_eq, hn_eq]
  exact (Nat.fib_lt_fib (by omega)).mpr (by omega)

/-- Property 8: Every `prime_fib n` for `2 ≤ n` within the search bound is strictly greater
than 2 and odd (`prime_fib n % 2 = 1`). -/
def odd_of_ge_two_prop (n : Nat) : Prop :=
  2 ≤ n → n ≤ (prime_fib_list prime_fib_fuel).length →
    2 < prime_fib n ∧ prime_fib n % 2 = 1

theorem odd_of_ge_two_thm (n : Nat) : odd_of_ge_two_prop n := by
  intro hn2 hlen
  have h1_pre : Pre 1 := by unfold Pre; omega
  have hn_pre : Pre n := by unfold Pre; omega
  have h1_val : prime_fib 1 = 2 := by decide
  have hlt : prime_fib 1 < prime_fib n := strict_mono_thm 1 n h1_pre (by omega) hlen
  rw [h1_val] at hlt
  have hprime : Nat.Prime (prime_fib n) := is_prime_thm n hn_pre
  rcases Nat.Prime.eq_two_or_odd hprime with h2 | hodd
  · omega
  · exact ⟨hlt, hodd⟩

/-- Property 9: Fuel invariance — once `fuel₁` is sufficient to find `n` prime Fibonacci numbers,
any larger `fuel₂ ≥ fuel₁` produces the exact same result. -/
def fuel_invariance_prop (n fuel₁ fuel₂ : Nat) : Prop :=
  Pre n → n ≤ (prime_fib_list fuel₁).length → fuel₁ ≤ fuel₂ →
    prime_fib_loop fuel₁ 0 1 n = prime_fib_loop fuel₂ 0 1 n

theorem fuel_invariance_thm (n fuel₁ fuel₂ : Nat) : fuel_invariance_prop n fuel₁ fuel₂ := by
  intro hn hlen₁ hfuel
  have hlen₂ : n ≤ (prime_fib_list fuel₂).length :=
    le_trans hlen₁ (prime_fib_list_from_length_mono 0 hfuel)
  rcases prime_fib_loop_nth_spec fuel₁ 0 n (by unfold Pre at hn; omega) hlen₁ with
    ⟨d₁, _, hd₁_eq, hd₁_prime, hd₁_len⟩
  rcases prime_fib_loop_nth_spec fuel₂ 0 n (by unfold Pre at hn; omega) hlen₂ with
    ⟨d₂, _, hd₂_eq, hd₂_prime, hd₂_len⟩
  have hd_eq : d₁ = d₂ := prime_fib_index_unique 0 d₁ d₂ hd₁_prime hd₂_prime (hd₁_len.trans hd₂_len.symm)
  subst hd_eq
  exact hd₁_eq.trans hd₂_eq.symm

/-- Property 10: Doctest base values (`prime_fib 1 = 2`, ..., `prime_fib 5 = 89`). -/
def base_cases_prop : Prop :=
  prime_fib 1 = 2 ∧
  prime_fib 2 = 3 ∧
  prime_fib 3 = 5 ∧
  prime_fib 4 = 13 ∧
  prime_fib 5 = 89

theorem base_cases_thm : base_cases_prop := by
  unfold base_cases_prop
  decide

/-! ## 8. Post-condition -/

/-- Postcondition combining all core properties of `prime_fib n`. -/
def Post_prop (n : Nat) : Prop :=
  is_prime_prop n ∧
  is_fib_prop n ∧
  ge_two_prop n ∧
  pos_prop n ∧
  nth_in_list_prop n ∧
  nth_prime_fib_prop n ∧
  odd_of_ge_two_prop n

/-! ## 9. Property-Based Tests -/

-- Randomized PBTs via Plausible
#eval Plausible.Testable.check (∀ n : Nat, 1 ≤ n → is_prime (prime_fib n) = true)
#eval Plausible.Testable.check (∀ n : Nat, 1 ≤ n → is_fib (prime_fib n) = true)
#eval Plausible.Testable.check (∀ n : Nat, 1 ≤ n → 2 ≤ prime_fib n)
#eval Plausible.Testable.check (∀ n : Nat, 1 ≤ n → 0 < prime_fib n)
#eval Plausible.Testable.check (∀ n : Nat, 1 ≤ n →
  prime_fib n = (prime_fib_list prime_fib_fuel).getD (n - 1) 2)
#eval Plausible.Testable.check (∀ m n : Nat, 1 ≤ m → m < n → n ≤ 10 →
  prime_fib m < prime_fib n)
#eval Plausible.Testable.check (∀ n : Nat, 2 ≤ n → n ≤ 10 →
  2 < prime_fib n ∧ prime_fib n % 2 = 1)
#eval Plausible.Testable.check (∀ n : Nat, 1 ≤ n →
  is_prime (prime_fib n) = true ∧
  is_fib (prime_fib n) = true ∧
  2 ≤ prime_fib n ∧
  0 < prime_fib n ∧
  prime_fib n = (prime_fib_list prime_fib_fuel).getD (n - 1) 2)

-- Bounded exhaustive PBTs across admissible inputs
example : (List.range 10).all (fun i => is_prime (prime_fib (i + 1))) = true := by native_decide
example : (List.range 10).all (fun i => is_fib (prime_fib (i + 1))) = true := by native_decide
example : (List.range 10).all (fun i => decide (2 ≤ prime_fib (i + 1))) = true := by native_decide
example : (List.range 10).all (fun i => decide (0 < prime_fib (i + 1))) = true := by native_decide
example : (List.range 10).all (fun i =>
  prime_fib (i + 1) == (prime_fib_list prime_fib_fuel).getD i 2) = true := by native_decide
example : (List.range 10).all (fun i =>
  let n := i + 1
  (List.range prime_fib_fuel).any (fun d =>
    (prime_fib n == Nat.fib (d + 2)) &&
    is_prime (Nat.fib (d + 2)) &&
    ((prime_fib_list (d + 1)).length == n))) = true := by native_decide
example : (List.range 9).all (fun i =>
  decide (prime_fib (i + 1) < prime_fib (i + 2))) = true := by native_decide
example : (List.range 9).all (fun i =>
  let n := i + 2
  decide (2 < prime_fib n ∧ prime_fib n % 2 = 1)) = true := by native_decide
example : (List.range 10).all (fun i =>
  let n := i + 1
  prime_fib_loop 42 0 1 n == prime_fib_loop 45 0 1 n) = true := by native_decide
example : (List.range 10).all (fun i =>
  let n := i + 1
  is_prime (prime_fib n) &&
  is_fib (prime_fib n) &&
  decide (2 ≤ prime_fib n) &&
  decide (0 < prime_fib n) &&
  (prime_fib n == (prime_fib_list prime_fib_fuel).getD (n - 1) 2)) = true := by native_decide

/-! ## 10. Correctness Theorem (`Pre -> Post`) -/

theorem prime_fib_correct (n : Nat) (h : Pre n) : Post_prop n :=
  ⟨is_prime_thm n h,
   is_fib_thm n h,
   ge_two_thm n h,
   pos_thm n h,
   nth_in_list_thm n h,
   nth_prime_fib_thm n h,
   odd_of_ge_two_thm n⟩

/-! ## 11. Imperative Implementation -/

/-- Imperative implementation of `prime_fib` using `Id.run do` and mutable state. -/
def prime_fib_imp (n : Nat) : Nat := Id.run do
  if n == 0 then
    return 2
  let mut a : Nat := 0
  let mut b : Nat := 1
  let mut rem : Nat := n
  for _ in List.range prime_fib_fuel do
    let c := a + b
    a := b
    b := c
    rem := if is_prime c then rem - 1 else rem
    if rem == 0 then
      return c
  return 2

/-! ## 12. Imperative Tests -/

example : prime_fib_imp 1 = 2 := by native_decide
example : prime_fib_imp 2 = 3 := by native_decide
example : prime_fib_imp 3 = 5 := by native_decide
example : prime_fib_imp 4 = 13 := by native_decide
example : prime_fib_imp 5 = 89 := by native_decide
example : prime_fib_imp 6 = 233 := by native_decide
example : prime_fib_imp 7 = 1597 := by native_decide
example : prime_fib_imp 8 = 28657 := by native_decide
example : prime_fib_imp 9 = 514229 := by native_decide
example : prime_fib_imp 10 = 433494437 := by native_decide

#eval prime_fib_imp 1
#eval prime_fib_imp 2
#eval prime_fib_imp 3
#eval prime_fib_imp 4
#eval prime_fib_imp 5
#eval prime_fib_imp 6
#eval prime_fib_imp 7
#eval prime_fib_imp 8
#eval prime_fib_imp 9
#eval prime_fib_imp 10

#eval Plausible.Testable.check (∀ n : Nat, prime_fib n = prime_fib_imp n)
example : (List.range 10).all (fun i => prime_fib (i + 1) == prime_fib_imp (i + 1)) = true := by
  native_decide

/-! ## 13. Equivalence Theorem (Functional = Imperative) -/

private theorem forIn_loop_eq (xs : List Nat) (a b rem : Nat) :
    (Id.run do
      let r ← forIn xs (⟨none, a, b, rem⟩ : MProd (Option Nat) (MProd Nat (MProd Nat Nat))) fun _ r => do
        let a := r.snd.fst
        let b := r.snd.snd.fst
        let rem := r.snd.snd.snd
        let c := a + b
        let a := b
        let b := c
        let rem := if is_prime c = true then rem - 1 else rem
        if (rem == 0) = true then
          return ForInStep.done ⟨some c, a, b, rem⟩
        else do
          pure PUnit.unit
          return ForInStep.yield ⟨none, a, b, rem⟩
      match r.fst with
      | none => do
        pure PUnit.unit
        return 2
      | some a => return a) = prime_fib_loop xs.length a b rem := by
  induction xs generalizing a b rem with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, prime_fib_loop, List.forIn_cons, bind, pure, Id.run]
    by_cases hr : ((if is_prime (a + b) = true then rem - 1 else rem) == 0) = true
    · simp [hr]
    · simp only [hr, Bool.false_eq_true, ↓reduceIte]
      exact ih b (a + b) (if is_prime (a + b) = true then rem - 1 else rem)

/-- Full functional-imperative equivalence theorem for all `n : Nat`. -/
theorem prime_fib_equiv (n : Nat) : prime_fib n = prime_fib_imp n := by
  unfold prime_fib prime_fib_imp
  by_cases hn : (n == 0) = true
  · simp [hn, Id.run, pure]
  · simp only [hn, Bool.false_eq_true, ↓reduceIte, bind, pure]
    rw [← List.length_range (n := prime_fib_fuel)]
    exact (forIn_loop_eq (List.range prime_fib_fuel) 0 1 n).symm

theorem prime_fib_eq_prime_fib_imp : prime_fib = prime_fib_imp :=
  funext prime_fib_equiv

end humaneval_39_prime_fib
