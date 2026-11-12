import Mathlib

/-!
Translation of HumanEval/39, `prime_fib`.

The input is an integer, as in Python. Fibonacci values and primality are exact
natural-number operations; Mathlib's verified primality decision procedure
implements the mathematical intent of the source's trial division.

`prime_fib` uses verified partial recursion: `some v` means the Python loop
returns `v`, while `none` denotes divergence (it is not a runtime timeout).
In particular, input zero returns 1 and negative inputs diverge. Infinitely many
Fibonacci primes is an open problem, so no totality assumption is imposed on
positive inputs. We prove the precise termination criterion instead.

`prime_fib_bounded` exposes finite observations for exhaustive property tests;
its fuel is not a restriction on the unbounded implementation or its theorems.
-/

namespace humaneval_39_prime_fib

def is_prime (p : Nat) : Bool := decide (Nat.Prime p)

/-- The value appended at iteration `k`, starting with iteration zero. -/
def fibAt (k : Nat) : Nat := Nat.fib (k + 2)

/-- Number of prime values among the first `k` appended Fibonacci values. -/
def primeCount : Nat → Nat
  | 0 => 0
  | k + 1 => primeCount k + if is_prime (fibAt k) then 1 else 0

/-- Functional search: the Python counter is `n - primeCount (k + 1)`. -/
def seek (n : Int) (k : Nat) : Option Nat :=
  if (primeCount (k + 1) : Int) = n then some (fibAt k)
  else seek n (k + 1)
partial_fixpoint

def prime_fib (n : Int) : Option Nat := seek n 0

def seekFuel : Nat → Int → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, n, k =>
      if (primeCount (k + 1) : Int) = n then some (fibAt k)
      else seekFuel fuel n (k + 1)

def prime_fib_bounded (fuel : Nat) (n : Int) : Option Nat := seekFuel fuel n 0

example : prime_fib 1 = some 2 := by native_decide
example : prime_fib 2 = some 3 := by native_decide
example : prime_fib 3 = some 5 := by native_decide
example : prime_fib 4 = some 13 := by native_decide
example : prime_fib 5 = some 89 := by native_decide
example : prime_fib 6 = some 233 := by native_decide
example : prime_fib 7 = some 1597 := by native_decide
example : prime_fib 8 = some 28657 := by native_decide
example : prime_fib 9 = some 514229 := by native_decide
example : prime_fib 10 = some 433494437 := by native_decide
example : prime_fib 0 = some 1 := by native_decide
#eval (List.range 11).map (fun n => prime_fib (n : Int))

/-- The documented, one-based input domain; no unproved totality hypothesis. -/
def Pre (n : Int) : Prop := 0 < n

theorem is_prime_iff (p : Nat) : is_prime p = true ↔ Nat.Prime p := by
  simp [is_prime]

/-- Exact integer-square-root version of the Python helper's trial range. -/
theorem is_prime_trial_division (p : Nat) :
    is_prime p = true ↔ 2 ≤ p ∧
      ∀ k, 2 ≤ k → k < min (Nat.sqrt p + 1) (p - 1) → p % k ≠ 0 := by
  rw [is_prime_iff, Nat.prime_def_le_sqrt]
  constructor
  · rintro ⟨h2, hdiv⟩
    refine ⟨h2, ?_⟩
    intro k hk hbound hmod
    have hb := (lt_min_iff.mp hbound).1
    exact hdiv k hk (by omega) (Nat.dvd_of_mod_eq_zero hmod)
  · rintro ⟨h2, hdiv⟩
    refine ⟨h2, ?_⟩
    intro k hk hsqrt hdvd
    have hsq : k * k ≤ p := Nat.le_sqrt.mp hsqrt
    have hkp : k + 1 < p := by nlinarith
    exact hdiv k hk (lt_min (by omega) (by omega)) (Nat.mod_eq_zero_of_dvd hdvd)

theorem primeCount_step (k : Nat) :
    primeCount (k + 1) = primeCount k + if is_prime (fibAt k) then 1 else 0 := rfl

theorem primeCount_mono : Monotone primeCount := by
  apply monotone_nat_of_le_succ
  intro k
  rw [primeCount_step]
  omega

theorem primeCount_eq_length (k : Nat) :
    primeCount k = ((List.range k).filter (fun i => is_prime (fibAt i))).length := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [primeCount_step, List.range_succ, List.filter_append, ih,
        List.filter_cons, List.filter_nil]
      split <;> simp_all

/-- Exact first-hit semantics, including zero and negative counters. -/
theorem seek_sound (n : Int) : ∀ k v, seek n k = some v →
    ∃ j, k ≤ j ∧ fibAt j = v ∧ (primeCount (j + 1) : Int) = n ∧
      ∀ i, k ≤ i → i < j → (primeCount (i + 1) : Int) ≠ n := by
  apply seek.partial_correctness
  intro rec ih k v h
  split at h
  · rename_i hc
    cases h
    exact ⟨k, le_rfl, rfl, hc, by omega⟩
  · rename_i hc
    obtain ⟨j, hj, hv, hn, hmin⟩ := ih (k + 1) v h
    refine ⟨j, by omega, hv, hn, ?_⟩
    intro i hki hij
    by_cases he : i = k
    · simpa [he] using hc
    · exact hmin i (by omega) hij

theorem seek_complete (n : Int) {j : Nat}
    (hn : (primeCount (j + 1) : Int) = n) :
    ∀ k, k ≤ j →
      (∀ i, k ≤ i → i < j → (primeCount (i + 1) : Int) ≠ n) →
      seek n k = some (fibAt j) := by
  intro k hk hmin
  induction h : j - k generalizing k with
  | zero =>
      have : k = j := by omega
      subst k
      rw [seek.eq_def, if_pos hn]
  | succ d ih =>
      have hkj : k < j := by omega
      rw [seek.eq_def, if_neg (hmin k le_rfl hkj)]
      apply ih (k + 1) (by omega)
      · intro i hki hij
        exact hmin i (by omega) hij
      · omega

theorem seekFuel_sound : ∀ fuel n k v, seekFuel fuel n k = some v → seek n k = some v := by
  intro fuel
  induction fuel with
  | zero => simp [seekFuel]
  | succ fuel ih =>
      intro n k v h
      simp only [seekFuel] at h
      rw [seek.eq_def]
      split at h <;> rename_i hc
      · simpa [hc] using h
      · simpa [hc] using ih n (k + 1) v h

theorem seekFuel_complete (n : Int) {j : Nat}
    (hn : (primeCount (j + 1) : Int) = n) :
    ∀ fuel k, k ≤ j → j < k + fuel →
      (∀ i, k ≤ i → i < j → (primeCount (i + 1) : Int) ≠ n) →
      seekFuel fuel n k = some (fibAt j) := by
  intro fuel
  induction fuel with
  | zero => intros; omega
  | succ fuel ih =>
      intro k hk hbound hmin
      by_cases he : k = j
      · subst k
        simp [seekFuel, hn]
      · have hkj : k < j := by omega
        rw [seekFuel, if_neg (hmin k le_rfl hkj)]
        apply ih (k + 1) (by omega) (by omega)
        intro i hki hij
        exact hmin i (by omega) hij

/-- Finite observations characterize the unbounded program without a fuel cap. -/
theorem bounded_observations (n : Int) (v : Nat) :
    prime_fib n = some v ↔ ∃ fuel, prime_fib_bounded fuel n = some v := by
  constructor
  · intro hv
    obtain ⟨j, hj, he, hc, hm⟩ := seek_sound n 0 v hv
    refine ⟨j + 1, ?_⟩
    rw [← he]
    exact seekFuel_complete n hc (j + 1) 0 hj (by omega) hm
  · rintro ⟨fuel, h⟩
    exact seekFuel_sound fuel n 0 v h

theorem first_hit_prime {n : Int} {j : Nat} (hn : 0 < n)
    (hc : (primeCount (j + 1) : Int) = n)
    (hmin : ∀ i, i < j → (primeCount (i + 1) : Int) ≠ n) :
    Nat.Prime (fibAt j) := by
  apply (is_prime_iff _).mp
  by_contra hp
  have he : is_prime (fibAt j) = false := Bool.eq_false_iff.mpr hp
  rw [primeCount_step, he] at hc
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hc
  cases j with
  | zero => simp [primeCount] at hc; omega
  | succ j => exact hmin j (by omega) hc

theorem prime_hit_first {n : Int} {j : Nat}
    (hp : Nat.Prime (fibAt j)) (hc : (primeCount (j + 1) : Int) = n) :
    ∀ i, i < j → (primeCount (i + 1) : Int) ≠ n := by
  have hs := primeCount_step j
  rw [(is_prime_iff _).mpr hp] at hs
  simp only [↓reduceIte] at hs
  intro i hij
  have hm := primeCount_mono (show i + 1 ≤ j by omega)
  omega

def prime_prop (n : Int) : Prop :=
  ∀ v, prime_fib n = some v → Nat.Prime v

theorem prime_thm (n : Int) (hn : Pre n) : prime_prop n := by
  intro v hv
  obtain ⟨j, _, hj, hc, hm⟩ := seek_sound n 0 v hv
  rw [← hj]
  exact first_hit_prime hn hc (fun i hi => hm i (Nat.zero_le _) hi)

def fibonacci_prop (n : Int) : Prop :=
  ∀ v, prime_fib n = some v → ∃ k, Nat.fib k = v

theorem fibonacci_thm (n : Int) : fibonacci_prop n := by
  intro v hv
  obtain ⟨j, _, hj, _, _⟩ := seek_sound n 0 v hv
  exact ⟨j + 2, hj⟩

/-- The returned prime has exactly `n - 1` preceding Fibonacci primes. -/
def rank_prop (n : Int) : Prop :=
  ∀ v, prime_fib n = some v →
    ∃ j, fibAt j = v ∧ (primeCount j : Int) = n - 1 ∧
      (primeCount (j + 1) : Int) = n

theorem rank_thm (n : Int) (hn : Pre n) : rank_prop n := by
  intro v hv
  obtain ⟨j, _, hj, hc, hm⟩ := seek_sound n 0 v hv
  have hp := first_hit_prime hn hc (fun i hi => hm i (Nat.zero_le _) hi)
  have hs := primeCount_step j
  rw [(is_prime_iff _).mpr hp] at hs
  simp only [↓reduceIte] at hs
  exact ⟨j, hj, by omega, hc⟩

/-- Both directions of the specification of the n-th prime Fibonacci value. -/
theorem nth_characterization (n : Int) (hn : Pre n) (v : Nat) :
    prime_fib n = some v ↔ Nat.Prime v ∧
      ∃ j, fibAt j = v ∧ (primeCount j : Int) = n - 1 := by
  constructor
  · intro hv
    obtain ⟨j, hj, hc, _⟩ := rank_thm n hn v hv
    exact ⟨prime_thm n hn v hv, j, hj, hc⟩
  · rintro ⟨hp, j, hj, hc⟩
    have hpj : Nat.Prime (fibAt j) := hj ▸ hp
    have hs := primeCount_step j
    rw [(is_prime_iff _).mpr hpj] at hs
    simp only [↓reduceIte] at hs
    have hcount : (primeCount (j + 1) : Int) = n := by omega
    rw [← hj]
    exact seek_complete n hcount 0 (Nat.zero_le _)
      (fun i _ hi => prime_hit_first hpj hcount i hi)

/-- Termination is equivalent to existence of the requested Fibonacci prime. -/
def termination_prop (n : Int) : Prop :=
  (∃ v, prime_fib n = some v) ↔
    ∃ j, Nat.Prime (fibAt j) ∧ (primeCount (j + 1) : Int) = n

theorem termination_thm (n : Int) (hn : Pre n) : termination_prop n := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨j, _, hj, hc, _⟩ := seek_sound n 0 v hv
    exact ⟨j, hj ▸ prime_thm n hn v hv, hc⟩
  · rintro ⟨j, hp, hc⟩
    exact ⟨fibAt j, seek_complete n hc 0 (Nat.zero_le _) (fun i _ hi =>
      prime_hit_first hp hc i hi)⟩

/-- Increasing requested ranks give strictly increasing returned values. -/
def order_prop (n : Int) : Prop :=
  ∀ m v w, n < m → prime_fib n = some v → prime_fib m = some w → v < w

theorem order_thm (n : Int) : order_prop n := by
  intro m v w hnm hv hw
  obtain ⟨j, _, hj, hcj, _⟩ := seek_sound n 0 v hv
  obtain ⟨k, _, hk, hck, _⟩ := seek_sound m 0 w hw
  have hjk : j < k := by
    by_contra h
    have hm := primeCount_mono (show k + 1 ≤ j + 1 by omega)
    omega
  rw [← hj, ← hk]
  exact Nat.fib_add_two_strictMono hjk

theorem zero_input : prime_fib 0 = some 1 := by
  rw [prime_fib, seek.eq_def]
  norm_num [primeCount, is_prime, fibAt]

/-- `none` here denotes nontermination, rather than an exception or a return value. -/
theorem negative_input (n : Int) (hn : n < 0) : prime_fib n = none := by
  cases h : prime_fib n with
  | none => rfl
  | some v =>
      obtain ⟨j, _, _, hc, _⟩ := seek_sound n 0 v h
      omega

def Post_prop (n : Int) : Prop :=
  prime_prop n ∧ fibonacci_prop n ∧ rank_prop n ∧ termination_prop n ∧ order_prop n

/- Property-based tests. Each check uses the finite observation proved above.
   Returning `none` within a budget only means that no return was observed yet.
   The existential termination criterion is not decidable in general; its
   executable counterpart compares termination within a budget with existence
   of the requested prime within exactly the same prefix. -/

def primeCheck (fuel : Nat) (n : Int) : Bool :=
  match prime_fib_bounded fuel n with
  | none => true
  | some v => is_prime v

def fibonacciCheck (fuel : Nat) (n : Int) : Bool :=
  match prime_fib_bounded fuel n with
  | none => true
  | some v => (List.range fuel).any (fun j => fibAt j == v)

def rankCheck (fuel : Nat) (n : Int) : Bool :=
  match prime_fib_bounded fuel n with
  | none => true
  | some v => (List.range fuel).any (fun j =>
      fibAt j == v && (primeCount j : Int) == n - 1 &&
        (primeCount (j + 1) : Int) == n)

def terminationCheck (fuel : Nat) (n : Int) : Bool :=
  (prime_fib_bounded fuel n).isSome ==
    (List.range fuel).any (fun j => is_prime (fibAt j) && (primeCount (j + 1) : Int) == n)

def orderCheck (fuel : Nat) (n m : Int) : Bool :=
  match prime_fib_bounded fuel n, prime_fib_bounded fuel m with
  | some v, some w => decide (n < m → v < w)
  | _, _ => true

def postCheck (fuel : Nat) (n : Int) : Bool :=
  primeCheck fuel n && fibonacciCheck fuel n && rankCheck fuel n &&
    terminationCheck fuel n && (List.range 13).all (fun m => orderCheck fuel n (m : Int))

-- PBT for the primality helper, using exhaustive division as an independent check.
example : (List.range 300).all (fun p => is_prime p ==
    (decide (2 ≤ p) && (List.range (p - 2)).all (fun k => p % (k + 2) != 0))) = true := by
  native_decide

-- PBT for prime_prop: every budget from 0 through 44, ranks 1 through 12.
example : (List.range 45).all (fun fuel =>
    (List.range 12).all (fun n => primeCheck fuel (n + 1))) = true := by native_decide

-- PBT for fibonacci_prop, including zero and negative inputs.
example : (List.range 45).all (fun fuel =>
    (List.range 16).all (fun n => fibonacciCheck fuel ((n : Int) - 3))) = true := by native_decide

-- PBT for rank_prop.
example : (List.range 45).all (fun fuel =>
    (List.range 12).all (fun n => rankCheck fuel (n + 1))) = true := by native_decide

-- PBT for termination_prop: the finite-prefix executable counterpart.
example : (List.range 45).all (fun fuel =>
    (List.range 12).all (fun n => terminationCheck fuel (n + 1))) = true := by native_decide

-- PBT for order_prop; includes input zero and unattained ranks within the budget.
example : (List.range 13).all (fun n =>
    (List.range 13).all (fun m => orderCheck 44 n m)) = true := by native_decide

-- PBT for the complete post-condition.
example : (List.range 45).all (fun fuel =>
    (List.range 12).all (fun n => postCheck fuel (n + 1))) = true := by native_decide

theorem correctness (n : Int) : Pre n → Post_prop n := by
  intro hn
  exact ⟨prime_thm n hn, fibonacci_thm n, rank_thm n hn, termination_thm n hn, order_thm n⟩

/-- One imperative loop iteration, with the source's two Fibonacci registers
    and its decreasing integer counter. The return test follows the decrement. -/
def imperativeBody (nextIteration : Int → Nat → Nat → Option Nat)
    (remaining : Int) (previous current : Nat) : Option Nat := Id.run do
  let mut a := previous
  let mut b := current
  let mut left := remaining
  let next := a + b
  a := b
  b := next
  if is_prime b then
    left := left - 1
  if left = 0 then
    return some b
  else
    return nextIteration left a b

def imperativeLoop (remaining : Int) (previous current : Nat) : Option Nat :=
  imperativeBody imperativeLoop remaining previous current
partial_fixpoint monotonicity by
  intro f g h remaining previous current
  dsimp [imperativeBody, Id.run]
  split <;> split
  all_goals first | apply Lean.Order.PartialOrder.rel_refl | exact h _ _ _

def prime_fib_imperative (n : Int) : Option Nat := Id.run do
  return imperativeLoop n 0 1

example : prime_fib_imperative 1 = some 2 := by native_decide
example : prime_fib_imperative 2 = some 3 := by native_decide
example : prime_fib_imperative 3 = some 5 := by native_decide
example : prime_fib_imperative 4 = some 13 := by native_decide
example : prime_fib_imperative 5 = some 89 := by native_decide
example : prime_fib_imperative 6 = some 233 := by native_decide
example : prime_fib_imperative 7 = some 1597 := by native_decide
example : prime_fib_imperative 8 = some 28657 := by native_decide
example : prime_fib_imperative 9 = some 514229 := by native_decide
example : prime_fib_imperative 10 = some 433494437 := by native_decide
example : prime_fib_imperative 0 = some 1 := by native_decide
#eval (List.range 11).map (fun n => prime_fib_imperative (n : Int))

theorem imperativeBody_invariant (rec : Int → Nat → Nat → Option Nat) (n : Int) (k : Nat) :
    imperativeBody rec (n - primeCount k) (Nat.fib k) (Nat.fib (k + 1)) =
      if (primeCount (k + 1) : Int) = n then some (fibAt k)
      else rec (n - primeCount (k + 1)) (Nat.fib (k + 1)) (Nat.fib (k + 2)) := by
  have hf : Nat.fib k + Nat.fib (k + 1) = fibAt k := (Nat.fib_add_two).symm
  dsimp [imperativeBody, Id.run]
  rw [hf]
  by_cases hp : is_prime (fibAt k) = true
  · simp only [hp, ↓reduceIte, primeCount_step, Nat.cast_add, Nat.cast_one]
    have he : n - (primeCount k : Int) - 1 = n - ((primeCount k : Int) + 1) := by omega
    have hz : n - ((primeCount k : Int) + 1) = 0 ↔ (primeCount k : Int) + 1 = n := by omega
    simp [hz, he, fibAt, pure, bind]
  · simp only [hp, primeCount_step]
    have hz : n - (primeCount k : Int) = 0 ↔ (primeCount k : Int) = n := by omega
    simp [hz, fibAt, pure, bind]

theorem imperative_to_functional : ∀ remaining previous current v,
    imperativeLoop remaining previous current = some v →
    ∀ n k, remaining = n - primeCount k → previous = Nat.fib k → current = Nat.fib (k + 1) →
      seek n k = some v := by
  apply imperativeLoop.partial_correctness
  intro rec ih remaining previous current v h n k hr ha hb
  subst remaining previous current
  rw [imperativeBody_invariant] at h
  rw [seek.eq_def]
  split at h <;> rename_i hc
  · simpa [hc] using h
  · simpa [hc] using ih _ _ _ v h n (k + 1) rfl rfl rfl

theorem functional_to_imperative (n : Int) : ∀ k v, seek n k = some v →
    imperativeLoop (n - primeCount k) (Nat.fib k) (Nat.fib (k + 1)) = some v := by
  apply seek.partial_correctness
  intro rec ih k v h
  rw [imperativeLoop.eq_def, imperativeBody_invariant]
  split at h <;> rename_i hc
  · simpa [hc] using h
  · simpa [hc] using ih (k + 1) v h

/-- Equality includes divergent executions, as well as all returned values. -/
theorem functional_eq_imperative (n : Int) : prime_fib n = prime_fib_imperative n := by
  apply Option.ext
  intro v
  constructor
  · intro h
    simpa [prime_fib_imperative, primeCount] using functional_to_imperative n 0 v h
  · intro h
    exact imperative_to_functional n 0 1 v h n 0 (by simp [primeCount]) rfl rfl

end humaneval_39_prime_fib
