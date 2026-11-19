import Mathlib
namespace Agent

/-!
# HumanEval 39: prime Fibonacci numbers

The input is a Python integer, modelled by `Int`; Fibonacci numbers are exact
natural numbers. `Nat.Prime` is the mathematical trial-division predicate (no
floating-point approximation to the square root is needed).

The Python loop is genuinely partial. In particular, termination on *all*
positive integers would assert infinitely many Fibonacci primes, an open
problem. `observe` executes any requested finite number of iterations;
`prime_fib : Int → Part Nat` retains the unbounded semantics. Exhausting an
observation's fuel is not a return value of the Python program. Zero returns
1 on the first iteration; negative inputs never return.
-/

namespace humaneval_39_prime_fib

/-- Python's trial division, with the integer square root in place of
`int(math.sqrt(p))`. Only the nonnegative Fibonacci candidates reach this helper.
The upper bound is exclusive, including the source's `min` and `p - 1`. -/
def is_prime (p : Nat) : Bool :=
  decide (2 ≤ p) && (List.range (min (Nat.sqrt p + 1) (p - 1))).all
    (fun k => decide (2 ≤ k → p % k ≠ 0))

/-- The number of prime candidates among F₂, ..., F_(k+1). -/
def primeCount : Nat → Nat
  | 0 => 0
  | k + 1 => primeCount k + if Nat.Prime (Nat.fib (k + 2)) then 1 else 0

/-- Functional execution, starting at candidate F_(k+2). -/
def scan : Nat → Nat → Int → Option Nat
  | 0, _, _ => none
  | fuel + 1, k, remaining =>
      let value := Nat.fib (k + 2)
      let next := remaining - if Nat.Prime value then 1 else 0
      if next = 0 then some value else scan fuel (k + 1) next

/-- A finite observation, not a fixed global search bound. -/
def observe (n : Int) (fuel : Nat) : Option Nat := scan fuel 0 n

/-- Complete a family of finite observations by selecting its first success.
This does not decide whether a successful observation exists. -/
noncomputable def completion (f : Nat → Option Nat) : Part Nat :=
  ⟨∃ fuel, (f fuel).isSome = true,
    fun h => (f (Nat.find h)).getD 0⟩

/-- Unbounded partial result: a terminating finite execution supplies its value. -/
noncomputable def prime_fib (n : Int) : Part Nat := completion (observe n)

-- The ten public tests; 42 steps reach F₄₃, the tenth Fibonacci prime.
example : observe 1 42 = some 2 := by native_decide
example : observe 2 42 = some 3 := by native_decide
example : observe 3 42 = some 5 := by native_decide
example : observe 4 42 = some 13 := by native_decide
example : observe 5 42 = some 89 := by native_decide
example : observe 6 42 = some 233 := by native_decide
example : observe 7 42 = some 1597 := by native_decide
example : observe 8 42 = some 28657 := by native_decide
example : observe 9 42 = some 514229 := by native_decide
example : observe 10 42 = some 433494437 := by native_decide
#eval (List.range 10).map (fun i => observe (Int.ofNat (i + 1)) 42)
example : observe 0 1 = some 1 := by native_decide
example : observe (-1) 42 = none := by native_decide

/-- The documented n-th-prime contract uses positive, one-based indices.
The implementations themselves also model zero and negative integers. -/
def Pre (n : Int) : Prop := 0 < n



/-- Trial division is equivalent to mathematical primality, including 0,1,2,3. -/
@[simp] theorem is_prime_iff (p : Nat) : is_prime p = true ↔ Nat.Prime p := by
  simp only [is_prime, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨hp, htest⟩
    apply Nat.prime_def_le_sqrt.mpr
    refine ⟨hp, ?_⟩
    intro k hk hs
    have hsq : k * k ≤ p := Nat.le_sqrt.mp hs
    have hsub : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
    have hkp : k < p - 1 := by nlinarith
    have ht := htest k (lt_min (by omega) hkp) hk
    simpa only [Nat.dvd_iff_mod_eq_zero] using ht
  · intro hp
    obtain ⟨hp2, hdiv⟩ := Nat.prime_def_le_sqrt.mp hp
    refine ⟨hp2, ?_⟩
    intro k hk hk2
    have hs : k ≤ Nat.sqrt p := by have := (lt_min_iff.mp hk).1; omega
    simpa only [Nat.dvd_iff_mod_eq_zero] using hdiv k hk2 hs

/-- Once a finite execution returns, further fuel does not change its result. -/
theorem scan_stable {fuel k : Nat} {r : Int} {v : Nat}
    (h : scan fuel k r = some v) (extra : Nat) :
    scan (fuel + extra) k r = some v := by
  induction fuel generalizing k r with
  | zero => simp [scan] at h
  | succ fuel ih =>
      simp only [scan] at h
      rw [Nat.succ_add]
      simp only [scan]
      by_cases he : r - (if Nat.Prime (Nat.fib (k + 2)) then 1 else 0) = 0
      · simpa only [he, ↓reduceIte] using h
      · simp only [he, ↓reduceIte] at h ⊢
        exact ih h

theorem observe_unique {n : Int} {f g v w : Nat}
    (hv : observe n f = some v) (hw : observe n g = some w) : v = w := by
  have h₁ := scan_stable hv g
  have h₂ := scan_stable hw f
  rw [Nat.add_comm f g] at h₁
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-- This is the connection between executable observations and the partial function. -/
theorem mem_prime_fib_iff (n : Int) (v : Nat) :
    v ∈ prime_fib n ↔ ∃ fuel, observe n fuel = some v := by
  change (∃ h : ∃ fuel, (observe n fuel).isSome = true,
    (observe n (Nat.find h)).getD 0 = v) ↔ _
  constructor
  · rintro ⟨h, hv⟩
    have hs := Nat.find_spec h
    cases he : observe n (Nat.find h) with
    | none => simp [he] at hs
    | some w =>
        simp only [he, Option.getD_some] at hv
        exact ⟨Nat.find h, he.trans (congrArg some hv)⟩
  · rintro ⟨fuel, hf⟩
    have h : ∃ fuel, (observe n fuel).isSome = true := ⟨fuel, by simp [hf]⟩
    refine ⟨h, ?_⟩
    have hs := Nat.find_spec h
    cases he : observe n (Nat.find h) with
    | none => simp [he] at hs
    | some w => simpa [he] using observe_unique he hf

theorem primeCount_mono : Monotone primeCount := by
  apply monotone_nat_of_le_succ
  intro k
  simp only [primeCount]
  omega

/-- `primeCount` really is the length of the filtered prefix. -/
theorem primeCount_eq_length (k : Nat) :
    primeCount k = ((List.range k).filter
      (fun j => decide (Nat.Prime (Nat.fib (j + 2))))).length := by
  induction k with
  | zero => rfl
  | succ k ih =>
      by_cases hp : Nat.Prime (Nat.fib (k + 2)) <;>
        simp [primeCount, List.range_succ, List.filter_append, ih, hp]

/-- Invariant: the mutable counter is the original input minus primes seen. -/
theorem scan_count_step (fuel k : Nat) (n : Int) :
    scan (fuel + 1) k (n - (primeCount k : Int)) =
      if n = (primeCount (k + 1) : Int) then some (Nat.fib (k + 2))
      else scan fuel (k + 1) (n - (primeCount (k + 1) : Int)) := by
  by_cases hp : Nat.Prime (Nat.fib (k + 2))
  · simp only [scan, primeCount, hp, ↓reduceIte, Nat.cast_add, Nat.cast_one]
    have he : n - (primeCount k : Int) - 1 = n - ((primeCount k : Int) + 1) := by omega
    rw [he]
    simp only [sub_eq_zero]
  · simp [scan, primeCount, hp, sub_eq_zero]

/-- Exact first-return characterization; it also covers zero and negative inputs. -/
theorem scan_spec (fuel k : Nat) (n : Int) (v : Nat) :
    scan fuel k (n - (primeCount k : Int)) = some v ↔
      ∃ j, k ≤ j ∧ j < k + fuel ∧ v = Nat.fib (j + 2) ∧
        (primeCount (j + 1) : Int) = n ∧
        ∀ i, k ≤ i → i < j → (primeCount (i + 1) : Int) ≠ n := by
  induction fuel generalizing k with
  | zero => simp [scan]; omega
  | succ fuel ih =>
      rw [scan_count_step]
      by_cases he : n = (primeCount (k + 1) : Int)
      · simp only [he, ↓reduceIte, Option.some.injEq]
        constructor
        · intro hv
          exact ⟨k, le_rfl, by omega, hv.symm, rfl, by omega⟩
        · rintro ⟨j, hj, hbound, hv, hc, hfirst⟩
          have hjk : j = k := by
            by_contra hne
            have := hfirst k le_rfl (by omega)
            exact this rfl
          simpa [hjk] using hv.symm
      · simp only [he, ↓reduceIte, ih]
        constructor
        · rintro ⟨j, hj, hbound, hv, hc, hfirst⟩
          refine ⟨j, by omega, by omega, hv, hc, ?_⟩
          intro i hki hij
          by_cases hik : i = k
          · subst i; exact Ne.symm he
          · exact hfirst i (by omega) hij
        · rintro ⟨j, hj, hbound, hv, hc, hfirst⟩
          have hkj : k + 1 ≤ j := by
            by_contra hnot
            have hjk : j = k := by omega
            exact he (by simpa [hjk] using hc.symm)
          exact ⟨j, hkj, by omega, hv, hc, fun i hi hij => hfirst i (by omega) hij⟩

theorem observe_spec (n : Int) (fuel v : Nat) :
    observe n fuel = some v ↔
      ∃ k, k < fuel ∧ v = Nat.fib (k + 2) ∧
        (primeCount (k + 1) : Int) = n ∧
        ∀ j, j < k → (primeCount (j + 1) : Int) ≠ n := by
  simpa [observe, primeCount] using scan_spec fuel 0 n v



/-- The unbounded loop stops at the first prefix whose count equals the input. -/
theorem result_spec (n : Int) (v : Nat) :
    v ∈ prime_fib n ↔
      ∃ k, v = Nat.fib (k + 2) ∧ (primeCount (k + 1) : Int) = n ∧
        ∀ j, j < k → (primeCount (j + 1) : Int) ≠ n := by
  rw [mem_prime_fib_iff]
  constructor
  · rintro ⟨fuel, hf⟩
    obtain ⟨k, _, hv, hc, hfirst⟩ := (observe_spec n fuel v).mp hf
    exact ⟨k, hv, hc, hfirst⟩
  · rintro ⟨k, hv, hc, hfirst⟩
    exact ⟨k + 1, (observe_spec n (k + 1) v).mpr ⟨k, by omega, hv, hc, hfirst⟩⟩

/-- A positive target can be reached for the first time only at a prime. -/
theorem first_hit_prime {n : Int} {k : Nat} (hn : 0 < n)
    (hc : (primeCount (k + 1) : Int) = n)
    (hfirst : ∀ j, j < k → (primeCount (j + 1) : Int) ≠ n) :
    Nat.Prime (Nat.fib (k + 2)) := by
  by_contra hp
  have hc' : (primeCount k : Int) = n := by simpa [primeCount, hp] using hc
  cases k with
  | zero => simp [primeCount] at hc'; omega
  | succ k => exact hfirst k (by omega) hc'

/-- A returned value is prime. -/
def prime_prop (v : Nat) : Prop := Nat.Prime v

theorem prime_thm {n : Int} {v : Nat} (hn : Pre n) (hv : v ∈ prime_fib n) :
    prime_prop v := by
  obtain ⟨k, rfl, hc, hf⟩ := (result_spec n v).mp hv
  exact first_hit_prime hn hc hf

/-- A returned value belongs to the Fibonacci sequence. -/
def fibonacci_prop (v : Nat) : Prop := ∃ k, v = Nat.fib (k + 2)

theorem fibonacci_thm {n : Int} {v : Nat} (hv : v ∈ prime_fib n) :
    fibonacci_prop v := by
  obtain ⟨k, hv, _⟩ := (result_spec n v).mp hv
  exact ⟨k, hv⟩

/-- Exactly n-1 prime Fibonacci numbers precede the result; no earlier
prefix already reaches n. Indices k+2 enumerate Fibonacci values strictly
increasingly, so this is also the numerical rank among Fibonacci primes. -/
def rank_prop (n : Int) (v : Nat) : Prop :=
  ∃ k, v = Nat.fib (k + 2) ∧ (primeCount k : Int) = n - 1 ∧
    ∀ j, j < k → (primeCount (j + 1) : Int) < n

theorem rank_thm {n : Int} {v : Nat} (hn : Pre n) (hv : v ∈ prime_fib n) :
    rank_prop n v := by
  obtain ⟨k, hv, hc, hf⟩ := (result_spec n v).mp hv
  have hp := first_hit_prime hn hc hf
  have hcount : (primeCount k : Int) + 1 = n := by
    simpa [primeCount, hp] using hc
  refine ⟨k, hv, by omega, ?_⟩
  intro j hj
  have hm := primeCount_mono (show j + 1 ≤ k from by omega)
  have hm' : (primeCount (j + 1) : Int) ≤ (primeCount k : Int) := by exact_mod_cast hm
  omega

/-- Increasing positive ranks give increasing numerical results. -/
def order_prop (n m : Int) (x y : Nat) : Prop := n < m → x < y

theorem order_thm {n m : Int} {x y : Nat}
    (hx : x ∈ prime_fib n) (hy : y ∈ prime_fib m) : order_prop n m x y := by
  obtain ⟨i, rfl, hi, _⟩ := (result_spec n x).mp hx
  obtain ⟨j, rfl, hj, _⟩ := (result_spec m y).mp hy
  intro hnm
  have hij : i < j := by
    by_contra h
    have hmono := primeCount_mono (show j + 1 ≤ i + 1 from by omega)
    omega
  exact Nat.fib_add_two_strictMono hij

/-- Postcondition of a successful call with a positive input. -/
def Post_prop (n : Int) (v : Nat) : Prop :=
  prime_prop v ∧ fibonacci_prop v ∧ rank_prop n v

/-! ## Property-based tests

The existential Fibonacci/rank specifications are tested by searching the
finite prefix that was actually executed, retaining their original theorem
domains. `none` means only that this observation has not returned yet. Separate
success-characterization tests below check the converse, avoiding vacuous
checks of an implementation that always returns `none`.
-/

/-- Check a property whenever an observation returns. -/
def checkObserved (n : Int) (fuel : Nat) (p : Nat → Bool) : Bool :=
  match observe n fuel with
  | none => true
  | some v => p v

def fibonacciCheck (fuel v : Nat) : Bool :=
  (List.range fuel).any (fun k => v == Nat.fib (k + 2))

def rankCheck (n : Int) (fuel v : Nat) : Bool :=
  (List.range fuel).any (fun k =>
    (v == Nat.fib (k + 2)) && decide ((primeCount k : Int) = n - 1) &&
      (List.range k).all (fun j => decide ((primeCount (j + 1) : Int) < n)))

def postCheck (n : Int) (fuel v : Nat) : Bool :=
  decide (Nat.Prime v) && fibonacciCheck fuel v && rankCheck n fuel v

-- PBT for prime_prop: 12 positive ranks, each with 43 observation lengths.
example : (List.range 12).all (fun i => (List.range 43).all (fun fuel =>
    checkObserved (Int.ofNat (i + 1)) fuel (fun v => decide (Nat.Prime v)))) = true :=
  by native_decide

-- PBT for fibonacci_prop, also exercising zero and negative input handling.
example : (List.range 16).all (fun i => (List.range 43).all (fun fuel =>
    checkObserved (Int.ofNat i - 3) fuel (fibonacciCheck fuel))) = true :=
  by native_decide

-- PBT for rank_prop, including the count and all earlier prefixes.
example : (List.range 12).all (fun i => (List.range 43).all (fun fuel =>
    checkObserved (Int.ofNat (i + 1)) fuel
      (rankCheck (Int.ofNat (i + 1)) fuel))) = true := by native_decide

-- PBT for order_prop: all pairs of the first ten returned ranks.
example : (List.range 10).all (fun i => (List.range 10).all (fun j =>
    match observe (Int.ofNat (i + 1)) 42, observe (Int.ofNat (j + 1)) 42 with
    | some x, some y => decide ((Int.ofNat (i + 1)) < (Int.ofNat (j + 1)) → x < y)
    | _, _ => false)) = true := by native_decide

-- PBT for Post_prop: the conjunction, over all positive inputs in the grid.
example : (List.range 12).all (fun i => (List.range 43).all (fun fuel =>
    checkObserved (Int.ofNat (i + 1)) fuel
      (postCheck (Int.ofNat (i + 1)) fuel))) = true := by native_decide

-- The literal trial-division helper agrees with primality on 1,000 inputs.
example : (List.range 1000).all (fun p => is_prime p == decide (Nat.Prime p)) = true :=
  by native_decide

-- PBT of the exact success domain for finite observations. Unbounded Part.Dom
-- is not executable (it is an unbounded existential); this is its executable
-- finite-observation counterpart, not an assumed global termination bound.
example : (List.range 12).all (fun i => (List.range 43).all (fun fuel =>
    (observe (Int.ofNat (i + 1)) fuel).isSome ==
      (List.range fuel).any (fun k => decide (Nat.Prime (Nat.fib (k + 2)) ∧
        (primeCount k : Int) + 1 = Int.ofNat (i + 1))))) = true := by native_decide

#eval (List.range 10).all (fun i => checkObserved (Int.ofNat (i + 1)) 42
  (postCheck (Int.ofNat (i + 1)) 42))

/-- Partial correctness: no termination assumption about Fibonacci primes. -/
theorem correctness (n : Int) : Pre n → ∀ v, v ∈ prime_fib n → Post_prop n v := by
  intro hn v hv
  exact ⟨prime_thm hn hv, fibonacci_thm hv, rank_thm hn hv⟩

/-- The postcondition is sufficient as well: every specified n-th prime
is actually returned by the unbounded loop. -/
theorem post_complete {n : Int} {v : Nat} (h : Post_prop n v) : v ∈ prime_fib n := by
  rcases h with ⟨hp, _, k, hv, hc, hfirst⟩
  apply (result_spec n v).mpr
  refine ⟨k, hv, ?_, fun j hj => ne_of_lt (hfirst j hj)⟩
  have hpk : Nat.Prime (Nat.fib (k + 2)) := by simpa [hv] using hp
  simp only [primeCount, hpk, ↓reduceIte, Nat.cast_add, Nat.cast_one]
  omega

/-- Negative inputs cannot reach zero after subtracting nonnegative counts. -/
theorem negative_diverges {n : Int} (hn : n < 0) : ¬(prime_fib n).Dom := by
  intro h
  obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp h
  obtain ⟨k, _, hc, _⟩ := (result_spec n v).mp hv
  omega

/-- The Python code tests for zero after the first append, even when it is not prime. -/
theorem zero_result : prime_fib 0 = Part.some 1 := by
  have hv : 1 ∈ prime_fib 0 := by
    apply (mem_prime_fib_iff 0 1).mpr
    exact ⟨1, by norm_num [observe, scan, Nat.fib_add_two]⟩
  apply Part.ext
  intro v
  constructor
  · intro h
    have := Part.mem_unique h hv
    simp [this]
  · intro h
    have : v = 1 := by simpa using h
    simpa [this] using hv



/-- Exact termination domain. There is no hypothesis or assertion that
infinitely many Fibonacci primes exist. -/
theorem termination_iff (n : Int) :
    (prime_fib n).Dom ↔ n = 0 ∨
      ∃ k, Nat.Prime (Nat.fib (k + 2)) ∧ (primeCount k : Int) + 1 = n := by
  constructor
  · intro h
    by_cases hn : n = 0
    · exact Or.inl hn
    · obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp h
      obtain ⟨k, _, hc, hf⟩ := (result_spec n v).mp hv
      have hnpos : 0 < n := by omega
      have hp := first_hit_prime hnpos hc hf
      exact Or.inr ⟨k, hp, by simpa [primeCount, hp] using hc⟩
  · rintro (rfl | ⟨k, hp, hc⟩)
    · simp [zero_result]
    · apply Part.dom_iff_mem.mpr
      refine ⟨Nat.fib (k + 2), (result_spec n _).mpr ⟨k, rfl, ?_, ?_⟩⟩
      · simpa [primeCount, hp] using hc
      · intro j hj
        have hm := primeCount_mono (show j + 1 ≤ k from by omega)
        omega

/-- Full input/output graph, including the behavior outside the documented
positive-input contract. Together with termination_iff this specifies both
results and divergence, without replacing the unbounded Python loop by a cap. -/
theorem complete_spec (n : Int) (v : Nat) :
    v ∈ prime_fib n ↔ (n = 0 ∧ v = 1) ∨ (Pre n ∧ Post_prop n v) := by
  constructor
  · intro hv
    by_cases hn : n = 0
    · left
      exact ⟨hn, by simpa [hn, zero_result] using hv⟩
    · right
      obtain ⟨k, _, hc, _⟩ := (result_spec n v).mp hv
      have hnpos : Pre n := by unfold Pre; omega
      exact ⟨hnpos, correctness n hnpos v hv⟩
  · rintro (⟨rfl, rfl⟩ | ⟨_, hpost⟩)
    · simp [zero_result]
    · exact post_complete hpost

/-- Imperative observation of the Python loop. Keeping the last two list
entries is sufficient; the discarded prefix is never read by Python.
Recursion on fuel supplies finite observations of the unbounded while loop. -/
def scanImperative : Nat → Nat → Nat → Int → Option Nat
  | 0, _, _, _ => none
  | fuel + 1, a, b, n => Id.run do
      let mut previous := a
      let mut current := b
      let mut remaining := n
      let next := previous + current
      previous := current
      current := next
      if is_prime current then
        remaining := remaining - 1
      if remaining = 0 then
        return some current
      return scanImperative fuel previous current remaining

def observeImperative (n : Int) (fuel : Nat) : Option Nat :=
  scanImperative fuel 0 1 n

noncomputable def prime_fib_imperative (n : Int) : Part Nat :=
  completion (observeImperative n)

example : observeImperative 1 42 = some 2 := by native_decide
example : observeImperative 2 42 = some 3 := by native_decide
example : observeImperative 3 42 = some 5 := by native_decide
example : observeImperative 4 42 = some 13 := by native_decide
example : observeImperative 5 42 = some 89 := by native_decide
example : observeImperative 6 42 = some 233 := by native_decide
example : observeImperative 7 42 = some 1597 := by native_decide
example : observeImperative 8 42 = some 28657 := by native_decide
example : observeImperative 9 42 = some 514229 := by native_decide
example : observeImperative 10 42 = some 433494437 := by native_decide
example : observeImperative 0 1 = some 1 := by native_decide
example : observeImperative (-2) 20 = none := by native_decide
#eval (List.range 10).map (fun i => observeImperative (Int.ofNat (i + 1)) 42)

-- Bounded observational equivalence, including nonpositive inputs and fuel zero.
example : (List.range 16).all (fun i => (List.range 43).all (fun fuel =>
    observe (Int.ofNat i - 3) fuel == observeImperative (Int.ofNat i - 3) fuel)) = true :=
  by native_decide

/-- Unfolding one imperative iteration, including both counter branches. -/
theorem imperative_step (fuel a b : Nat) (n : Int) :
    scanImperative (fuel + 1) a b n =
      let next := a + b
      let r := n - if Nat.Prime next then 1 else 0
      if r = 0 then some next else scanImperative fuel b next r := by
  by_cases hp : Nat.Prime (a + b) <;> simp [scanImperative, hp] <;>
    split_ifs <;> rfl

/-- The mutable pair always equals consecutive Fibonacci numbers. -/
theorem scan_equivalence (fuel k : Nat) (r : Int) :
    scanImperative fuel (Nat.fib k) (Nat.fib (k + 1)) r = scan fuel k r := by
  induction fuel generalizing k r with
  | zero => rfl
  | succ fuel ih =>
      rw [imperative_step, ← Nat.fib_add_two]
      simp only [scan]
      by_cases he : r - (if Nat.Prime (Nat.fib (k + 2)) then 1 else 0) = 0
      · simp only [he, ↓reduceIte]
      · simp only [he, ↓reduceIte]
        exact ih (k + 1) _

theorem observe_equivalence (n : Int) (fuel : Nat) :
    observe n fuel = observeImperative n fuel := by
  simpa [observe, observeImperative] using (scan_equivalence fuel 0 n).symm

/-- Equality includes the domains: divergence is preserved, not just returned values. -/
theorem functional_eq_imperative (n : Int) : prime_fib n = prime_fib_imperative n := by
  exact congrArg completion (funext (observe_equivalence n))

end humaneval_39_prime_fib
end Agent
