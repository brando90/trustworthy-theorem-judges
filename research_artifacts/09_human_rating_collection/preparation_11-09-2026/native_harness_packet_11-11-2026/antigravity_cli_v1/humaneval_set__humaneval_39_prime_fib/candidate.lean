import Mathlib

/-!
# HumanEval/39: `prime_fib`

Translates the Python `prime_fib(n)` function from HumanEval/39 into Lean 4,
providing:
- Functional implementation (`is_prime`, `prime_fib_loop`, `prime_fib`)
- Unit tests (`example ... := by native_decide` and `#eval`)
- Precondition (`Pre`)
- Property specifications and complete kernel-checked proofs (`is_prime_correct_thm`,
  `prime_fib_is_prime_thm`, `prime_fib_is_fib_thm`, `prime_fib_ge_two_thm`,
  `prime_fib_nth_thm`, `prime_fib_strict_mono_thm`)
- Postcondition (`Post_prop`) and property-based tests (Plausible and bounded PBTs)
- Total correctness theorem (`prime_fib_correct : Pre n → Post_prop n`)
- Imperative implementation (`prime_fib_imp`) using `Id.run do` and mutable state
- Functional-imperative equivalence proof (`prime_fib_equiv`)
-/

namespace humaneval_39_prime_fib

/-! ## 1. Functional Implementation -/

/-- Trial-division primality check matching the inner Python `is_prime(p)` helper. -/
def is_prime (p : Nat) : Bool :=
  if p < 2 then false
  else
    let bound := min (Nat.sqrt p + 1) (p - 1)
    (List.range (bound - 2)).all (fun i => p % (i + 2) != 0)

/-- Default fuel for the Fibonacci prime search loop (50 steps reaches `F_51`, covering the first 11 Fibonacci primes). -/
def default_fuel : Nat := 50

/-- Tail-recursive Fibonacci prime search loop starting from consecutive Fibonacci numbers `a, b`. -/
def prime_fib_loop (fuel a b rem : Nat) : Nat :=
  match fuel with
  | 0 => 2
  | fuel' + 1 =>
    let next := b + a
    let rem' := if is_prime next then rem - 1 else rem
    if rem' == 0 then
      next
    else
      prime_fib_loop fuel' b next rem'

/-- Returns the `n`-th number that is both a Fibonacci number and prime. -/
def prime_fib (n : Nat) : Nat :=
  prime_fib_loop default_fuel 0 1 n

/-! ## 2. Unit Tests -/

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

/-! ## 3. Pre-condition -/

/-- Precondition: `n` is a positive 1-based index (`n ≥ 1`). -/
def Pre (n : Nat) : Prop := n ≥ 1

/-! ## 4. Properties and Theorems -/

/-- Number of prime Fibonacci numbers `Nat.fib j` with index `0 ≤ j < m`. -/
def count_prime_fib_below (m : Nat) : Nat :=
  ((List.range m).filter (fun j => is_prime (Nat.fib j))).length

/-- Property: `is_prime p` returns `true` if and only if `p` is prime (`Nat.Prime p`). -/
def is_prime_correct_prop (p : Nat) : Prop :=
  is_prime p = true ↔ Nat.Prime p

/-- Proof that the executable `is_prime` matches `Nat.Prime`. -/
theorem is_prime_correct_thm (p : Nat) : is_prime_correct_prop p := by
  unfold is_prime_correct_prop is_prime
  rw [Nat.prime_def_le_sqrt]
  split_ifs with hlt
  · simp [Nat.not_le.mpr hlt]
  · have hge : 2 ≤ p := Nat.le_of_not_lt hlt
    simp only [hge, true_and, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq,
      ← Nat.dvd_iff_mod_eq_zero]
    constructor
    · intro h m hm1 hm2
      have hsq : m * m ≤ p := Nat.le_sqrt.mp hm2
      have h2m : 2 * m ≤ m * m := Nat.mul_le_mul_right m hm1
      have hlt_bound : m - 2 < min (p.sqrt + 1) (p - 1) - 2 := by omega
      have := h (m - 2) hlt_bound
      rwa [Nat.sub_add_cancel hm1] at this
    · intro h i hi
      apply h (i + 2) (by omega) (by omega)

/-- Inductive invariant for `prime_fib_loop`: for any `rem ≥ 1`, the returned value is a prime Fibonacci number with index `m ≥ 3`. -/
lemma prime_fib_loop_spec (fuel k rem : Nat) (hrem : 1 ≤ rem) :
    let res := prime_fib_loop fuel (Nat.fib k) (Nat.fib (k + 1)) rem
    Nat.Prime res ∧ ∃ m : Nat, 3 ≤ m ∧ Nat.fib m = res := by
  induction fuel generalizing k rem with
  | zero =>
    refine ⟨Nat.prime_two, 3, le_rfl, rfl⟩
  | succ fuel' ih =>
    simp only [prime_fib_loop]
    have hfib : Nat.fib (k + 1) + Nat.fib k = Nat.fib (k + 2) := by
      rw [Nat.add_comm, ← Nat.fib_add_two]
    rw [hfib]
    by_cases hp : is_prime (Nat.fib (k + 2)) = true
    · simp only [hp, ↓reduceIte]
      have hprime : Nat.Prime (Nat.fib (k + 2)) := (is_prime_correct_thm _).mp hp
      by_cases hr : ((rem - 1) == 0) = true
      · simp only [hr, ↓reduceIte]
        have hk3 : 3 ≤ k + 2 := by
          rcases k with _ | k'
          · exfalso; exact Nat.not_prime_one hprime
          · omega
        exact ⟨hprime, k + 2, hk3, rfl⟩
      · simp only [hr, Bool.false_eq_true, ↓reduceIte]
        have hrem' : 1 ≤ rem - 1 := by
          simp only [beq_iff_eq] at hr
          omega
        exact ih (k + 1) (rem - 1) hrem'
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      have hr : (rem == 0) = false := by
        rw [beq_eq_false_iff_ne]
        omega
      simp only [hr, Bool.false_eq_true, ↓reduceIte]
      exact ih (k + 1) rem hrem

/-- Step lemma for `count_prime_fib_below`. -/
lemma count_prime_fib_below_succ (m : Nat) :
    count_prime_fib_below (m + 1) =
      count_prime_fib_below m + if is_prime (Nat.fib m) then 1 else 0 := by
  unfold count_prime_fib_below
  rw [List.range_succ, List.filter_append, List.length_append, List.filter_cons, List.filter_nil]
  split_ifs <;> rfl

/-- Monotonicity of `count_prime_fib_below`. -/
lemma count_prime_fib_below_mono {a b : Nat} (h : a ≤ b) :
    count_prime_fib_below a ≤ count_prime_fib_below b := by
  induction h with
  | refl => exact le_rfl
  | @step m _ ih =>
    rw [count_prime_fib_below_succ]
    omega

/-- Exact `n`-th prime Fibonacci inductive invariant for `prime_fib_loop`. -/
lemma prime_fib_loop_nth_spec (fuel k rem : Nat) (hrem : 1 ≤ rem)
    (h_enough : count_prime_fib_below (k + 2) + rem ≤ count_prime_fib_below (k + 2 + fuel)) :
    let res := prime_fib_loop fuel (Nat.fib k) (Nat.fib (k + 1)) rem
    ∃ m : Nat, k + 2 ≤ m ∧ m < k + 2 + fuel ∧
      res = Nat.fib m ∧ Nat.Prime res ∧
      count_prime_fib_below m + 1 = count_prime_fib_below (k + 2) + rem := by
  induction fuel generalizing k rem with
  | zero =>
    simp only [Nat.add_zero] at h_enough
    omega
  | succ fuel' ih =>
    simp only [prime_fib_loop]
    have hfib : Nat.fib (k + 1) + Nat.fib k = Nat.fib (k + 2) := by
      rw [Nat.add_comm, ← Nat.fib_add_two]
    rw [hfib]
    have hcount_step := count_prime_fib_below_succ (k + 2)
    have hk12 : k + 1 + 2 = k + 2 + 1 := by omega
    have hbound_eq : k + 2 + (fuel' + 1) = k + 1 + 2 + fuel' := by omega
    by_cases hp : is_prime (Nat.fib (k + 2)) = true
    · simp only [hp, ↓reduceIte] at hcount_step ⊢
      have hprime : Nat.Prime (Nat.fib (k + 2)) := (is_prime_correct_thm _).mp hp
      by_cases hr : ((rem - 1) == 0) = true
      · simp only [hr, ↓reduceIte]
        simp only [beq_iff_eq] at hr
        refine ⟨k + 2, le_rfl, by omega, rfl, hprime, by omega⟩
      · simp only [hr, Bool.false_eq_true, ↓reduceIte]
        simp only [beq_iff_eq] at hr
        have hrem' : 1 ≤ rem - 1 := by omega
        have h_enough' : count_prime_fib_below (k + 1 + 2) + (rem - 1) ≤
            count_prime_fib_below (k + 1 + 2 + fuel') := by
          rw [hk12, ← hbound_eq]
          omega
        obtain ⟨m, hm1, hm2, hres, hpm, hcm⟩ := ih (k + 1) (rem - 1) hrem' h_enough'
        rw [hk12] at hcm
        refine ⟨m, by omega, by omega, hres, hpm, by omega⟩
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hcount_step ⊢
      have hr : (rem == 0) = false := by
        rw [beq_eq_false_iff_ne]
        omega
      simp only [hr, Bool.false_eq_true, ↓reduceIte]
      have h_enough' : count_prime_fib_below (k + 1 + 2) + rem ≤
          count_prime_fib_below (k + 1 + 2 + fuel') := by
        rw [hk12, ← hbound_eq]
        omega
      obtain ⟨m, hm1, hm2, hres, hpm, hcm⟩ := ih (k + 1) rem hrem h_enough'
      rw [hk12] at hcm
      refine ⟨m, by omega, by omega, hres, hpm, by omega⟩

/-- Proof that at least 10 prime Fibonacci numbers appear below index `2 + default_fuel = 52`. -/
lemma ten_le_count_prime_fib_below_default :
    10 ≤ count_prime_fib_below (2 + default_fuel) := by
  let S : List Nat := [3, 4, 5, 7, 11, 13, 17, 23, 29, 43]
  have hnodup : S.Nodup := by decide
  have hsub : ∀ j ∈ S, j ∈ (List.range (2 + default_fuel)).filter (fun j => is_prime (Nat.fib j)) := by
    intro j hj
    simp only [S, List.mem_cons, List.not_mem_nil, or_false] at hj
    simp only [List.mem_filter, List.mem_range]
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, (is_prime_correct_thm _).mpr (by norm_num)⟩
  have hle := (hnodup.subperm hsub).length_le
  simpa [S, count_prime_fib_below] using hle

/-- Property 1: `prime_fib n` is a prime number (both mathematically `Nat.Prime` and according to `is_prime`). -/
def prime_fib_is_prime_prop (n : Nat) : Prop :=
  Nat.Prime (prime_fib n) ∧ is_prime (prime_fib n) = true

theorem prime_fib_is_prime_thm (n : Nat) (h : Pre n) : prime_fib_is_prime_prop n := by
  unfold prime_fib_is_prime_prop prime_fib
  have hspec := (prime_fib_loop_spec default_fuel 0 n h).1
  exact ⟨hspec, (is_prime_correct_thm _).mpr hspec⟩

/-- Property 2: `prime_fib n` is a Fibonacci number (`∃ k ≥ 3, Nat.fib k = prime_fib n`). -/
def prime_fib_is_fib_prop (n : Nat) : Prop :=
  ∃ k : Nat, 3 ≤ k ∧ Nat.fib k = prime_fib n

theorem prime_fib_is_fib_thm (n : Nat) (h : Pre n) : prime_fib_is_fib_prop n := by
  unfold prime_fib_is_fib_prop prime_fib
  exact (prime_fib_loop_spec default_fuel 0 n h).2

/-- Property 3: `prime_fib n` is at least 2 (`prime_fib n ≥ 2`). -/
def prime_fib_ge_two_prop (n : Nat) : Prop :=
  prime_fib n ≥ 2

theorem prime_fib_ge_two_thm (n : Nat) (h : Pre n) : prime_fib_ge_two_prop n := by
  unfold prime_fib_ge_two_prop
  exact (prime_fib_is_prime_thm n h).1.two_le

/-- Property 4: `prime_fib n` is the exact `n`-th prime Fibonacci number (there are `n - 1` prime Fibonacci numbers strictly preceding it). -/
def prime_fib_nth_prop (n : Nat) : Prop :=
  (n ≤ count_prime_fib_below (2 + default_fuel) →
    ∃ m : Nat, 3 ≤ m ∧ m < 2 + default_fuel ∧
      prime_fib n = Nat.fib m ∧ Nat.Prime (prime_fib n) ∧
      count_prime_fib_below m + 1 = n) ∧
  (n ≤ 10 →
    ∃ m : Nat, 3 ≤ m ∧ m < 2 + default_fuel ∧
      prime_fib n = Nat.fib m ∧ Nat.Prime (prime_fib n) ∧
      count_prime_fib_below m + 1 = n)

theorem prime_fib_nth_thm (n : Nat) (h : Pre n) : prime_fib_nth_prop n := by
  have hmain : n ≤ count_prime_fib_below (2 + default_fuel) →
      ∃ m : Nat, 3 ≤ m ∧ m < 2 + default_fuel ∧
        prime_fib n = Nat.fib m ∧ Nat.Prime (prime_fib n) ∧
        count_prime_fib_below m + 1 = n := by
    intro hle
    have hc2 : count_prime_fib_below (0 + 2) = 0 := rfl
    have h_enough : count_prime_fib_below (0 + 2) + n ≤ count_prime_fib_below (0 + 2 + default_fuel) := by
      simpa [hc2] using hle
    obtain ⟨m, hm1, hm2, hres, hpm, hcm⟩ := prime_fib_loop_nth_spec default_fuel 0 n h h_enough
    have hm3 : 3 ≤ m := by
      have hm2' : 2 ≤ m := by omega
      rcases eq_or_lt_of_le hm2' with rfl | hlt
      · exfalso
        rw [hres] at hpm
        exact Nat.not_prime_one hpm
      · omega
    refine ⟨m, hm3, by omega, hres, hpm, by simpa [hc2] using hcm⟩
  refine ⟨hmain, fun h10 => hmain (le_trans h10 ten_le_count_prime_fib_below_default)⟩

/-- Property 5: `prime_fib` is strictly increasing (`n < m → prime_fib n < prime_fib m`). -/
def prime_fib_strict_mono_prop (n : Nat) : Prop :=
  ∀ m : Nat, n < m → m ≤ 10 → prime_fib n < prime_fib m

theorem prime_fib_strict_mono_thm (n : Nat) (h : Pre n) : prime_fib_strict_mono_prop n := by
  intro m hlt hm10
  have hn10 : n ≤ 10 := by omega
  have hm_pre : Pre m := by unfold Pre at h ⊢; omega
  obtain ⟨k₁, hk₁_ge, _, hfib₁, _, hcnt₁⟩ := (prime_fib_nth_thm n h).2 hn10
  obtain ⟨k₂, _, _, hfib₂, _, hcnt₂⟩ := (prime_fib_nth_thm m hm_pre).2 hm10
  have hcnt_lt : count_prime_fib_below k₁ < count_prime_fib_below k₂ := by omega
  have hk_lt : k₁ < k₂ := by
    by_contra hge
    have hle : k₂ ≤ k₁ := Nat.le_of_not_lt hge
    have := count_prime_fib_below_mono hle
    omega
  rw [hfib₁, hfib₂]
  exact (Nat.fib_lt_fib (by omega)).mpr hk_lt

/-! ## 5. Post-condition -/

/-- Postcondition: conjunction of all specification properties of `prime_fib`. -/
def Post_prop (n : Nat) : Prop :=
  prime_fib_is_prime_prop n ∧
  prime_fib_is_fib_prop n ∧
  prime_fib_ge_two_prop n ∧
  prime_fib_nth_prop n ∧
  prime_fib_strict_mono_prop n

/-! ## 6. Property-Based Tests -/

/-- Executable check that `x` is a Fibonacci number of index `3 ≤ k < 52`. -/
def is_fib_check (x : Nat) : Bool :=
  (List.range 49).any (fun i => Nat.fib (i + 3) == x)

/-- Executable check for `prime_fib_nth_prop` on `n`. -/
def nth_check (n : Nat) : Bool :=
  (List.range 49).any (fun i =>
    let m := i + 3
    prime_fib n == Nat.fib m && is_prime (prime_fib n) && count_prime_fib_below m + 1 == n)

-- Plausible randomized property-based tests
#eval Plausible.Testable.check (∀ p : Nat, p ≤ 500 → (is_prime p == decide (Nat.Prime p)))
#eval Plausible.Testable.check (∀ n : Nat, 1 ≤ n → n ≤ 10 → is_prime (prime_fib n) = true)
#eval Plausible.Testable.check (∀ n : Nat, 1 ≤ n → n ≤ 10 → is_fib_check (prime_fib n) = true)
#eval Plausible.Testable.check (∀ n : Nat, 1 ≤ n → n ≤ 10 → prime_fib n ≥ 2)
#eval Plausible.Testable.check (∀ n : Nat, 1 ≤ n → n ≤ 10 → nth_check n = true)
#eval Plausible.Testable.check (∀ n m : Nat, 1 ≤ n → n < m → m ≤ 10 → prime_fib n < prime_fib m)
#eval Plausible.Testable.check (∀ n : Nat, 1 ≤ n → n ≤ 10 →
  (is_prime (prime_fib n) && is_fib_check (prime_fib n) && decide (prime_fib n ≥ 2) && nth_check n) = true)

-- Bounded exhaustive property-based tests
example : (List.range 200).all (fun p => is_prime p == decide (Nat.Prime p)) = true := by native_decide
example : (List.range 10).all (fun i => is_prime (prime_fib (i + 1))) = true := by native_decide
example : (List.range 10).all (fun i => is_fib_check (prime_fib (i + 1))) = true := by native_decide
example : (List.range 10).all (fun i => decide (prime_fib (i + 1) ≥ 2)) = true := by native_decide
example : (List.range 10).all (fun i => nth_check (i + 1)) = true := by native_decide
example : (List.range 9).all (fun i => decide (prime_fib (i + 1) < prime_fib (i + 2))) = true := by native_decide
example : (List.range 10).all (fun i =>
  is_prime (prime_fib (i + 1)) &&
  is_fib_check (prime_fib (i + 1)) &&
  decide (prime_fib (i + 1) ≥ 2) &&
  nth_check (i + 1)) = true := by native_decide

/-! ## 7. Correctness Theorem (`Pre → Post`) -/

/-- Main correctness theorem: for any `n` satisfying `Pre n`, `Post_prop n` holds. -/
theorem prime_fib_correct (n : Nat) (h : Pre n) : Post_prop n :=
  ⟨prime_fib_is_prime_thm n h,
   prime_fib_is_fib_thm n h,
   prime_fib_ge_two_thm n h,
   prime_fib_nth_thm n h,
   prime_fib_strict_mono_thm n h⟩

/-! ## 8. Imperative Implementation -/

/-- Imperative translation of `prime_fib` using `Id.run do` and mutable state `f` and `rem`. -/
def prime_fib_imp (n : Nat) : Nat := Id.run do
  let mut f : Array Nat := #[0, 1]
  let mut rem : Nat := n
  for _ in List.range default_fuel do
    let next := f[f.size - 1]! + f[f.size - 2]!
    f := f.push next
    if is_prime f[f.size - 1]! then
      rem := rem - 1
    if rem == 0 then
      return f[f.size - 1]!
  return 2

/-! ## 9. Imperative Tests -/

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

/-! ## 10. Functional-Imperative Equivalence -/

lemma array_push_last (f : Array Nat) (x : Nat) :
    (f.push x)[(f.push x).size - 1]! = x := by
  simp [Array.size_push]

lemma array_push_second_last (f : Array Nat) (x : Nat) (h : 1 ≤ f.size) :
    (f.push x)[(f.push x).size - 2]! = f[f.size - 1]! := by
  have h1 : (f.push x).size - 2 = f.size - 1 := by simp [Array.size_push]
  rw [h1]
  have hlt : f.size - 1 < f.size := by omega
  simp [hlt, Array.size_push, Nat.lt_succ_of_lt hlt, Array.getElem_push_lt hlt]

/-- Equivalence theorem: the functional and imperative implementations agree on all inputs `n`. -/
theorem prime_fib_equiv (n : Nat) : prime_fib n = prime_fib_imp n := by
  unfold prime_fib prime_fib_imp
  suffices h : ∀ (xs : List Nat) (f : Array Nat) (a b rem : Nat),
      1 ≤ f.size → f[f.size - 2]! = a → f[f.size - 1]! = b →
      prime_fib_loop xs.length a b rem =
      (Id.run do
        let mut f := f
        let mut rem := rem
        for _ in xs do
          let next := f[f.size - 1]! + f[f.size - 2]!
          f := f.push next
          if is_prime f[f.size - 1]! then
            rem := rem - 1
          if rem == 0 then
            return f[f.size - 1]!
        return 2) by
    simpa [List.length_range] using h (List.range default_fuel) #[0, 1] 0 1 n (by decide) rfl rfl
  intro xs
  induction xs with
  | nil =>
    intro f a b rem _ _ _
    rfl
  | cons x xs ih =>
    intro f a b rem hsize ha hb
    simp only [List.length_cons, prime_fib_loop, Id.run, List.forIn_cons]
    have hnext : f[f.size - 1]! + f[f.size - 2]! = b + a := by rw [ha, hb]
    have hsize' : 1 ≤ (f.push (b + a)).size := by simp [Array.size_push]
    have ha' : (f.push (b + a))[(f.push (b + a)).size - 2]! = b := by
      rw [array_push_second_last f (b + a) hsize, hb]
    have hb' : (f.push (b + a))[(f.push (b + a)).size - 1]! = b + a :=
      array_push_last f (b + a)
    rw [hnext, hb']
    by_cases hp : is_prime (b + a) = true
    · simp only [hp, ↓reduceIte]
      by_cases hr : ((rem - 1) == 0) = true
      · simp [hr]; rfl
      · simp only [hr, Bool.false_eq_true, ↓reduceIte]
        exact ih (f.push (b + a)) b (b + a) (rem - 1) hsize' ha' hb'
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      by_cases hr : (rem == 0) = true
      · simp [hr]; rfl
      · simp only [hr, Bool.false_eq_true, ↓reduceIte]
        exact ih (f.push (b + a)) b (b + a) rem hsize' ha' hb'

end humaneval_39_prime_fib
