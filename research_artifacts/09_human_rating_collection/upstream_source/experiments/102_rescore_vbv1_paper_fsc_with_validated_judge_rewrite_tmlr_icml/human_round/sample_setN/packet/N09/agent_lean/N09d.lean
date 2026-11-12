import Mathlib

/-!
# HumanEval 39: prime Fibonacci numbers

The unbounded search is intentionally partial: infinitude of Fibonacci primes
is not assumed. The integer input zero returns the first appended value, 1;
negative inputs do not return. `some r` represents a Python return of `r`;
`none` is the least-fixpoint meaning of divergence, not an extra Python return.
In particular, evaluating the unbounded search on a divergent input still
runs forever. Finite observations are used to test those inputs safely.

Primality is mathematical natural-number primality, using exact arithmetic
instead of Python's floating square root. This preserves the discrete numeric
intent of the problem and does not assert facts about IEEE-754 rounding.
-/
namespace humaneval_39_prime_fib

/-- Tail-recursive search. `a,b` are consecutive Fibonacci numbers. -/
def search (n : Int) (a b : Nat) : Option Nat :=
  let c := a + b
  let next := if Nat.Prime c then n - 1 else n
  if next = 0 then some c else search next b c
partial_fixpoint

/-- The Python loop, including its special behavior at zero. -/
def prime_fib (n : Int) : Option Nat := search n 0 1

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
#eval (List.range 11).map (fun n => prime_fib n)

/-- All Python integer inputs are represented; `none` is semantic divergence,
not an exception returned by the running Python code. -/
def Pre (_n : Int) : Prop := True

/-- Number of prime Fibonacci values at indices strictly below `k`. -/
def primeCount : Nat → Nat
  | 0 => 0
  | k + 1 => primeCount k + if Nat.Prime (Nat.fib k) then 1 else 0

/-- One finite execution derivation of the unbounded loop. -/
inductive Runs : Int → Nat → Nat → Nat → Prop
  | done (n : Int) (a b : Nat)
      (stop : (if Nat.Prime (a + b) then n - 1 else n) = 0) :
      Runs n a b (a + b)
  | step {n : Int} {a b r : Nat}
      (cont : (if Nat.Prime (a + b) then n - 1 else n) ≠ 0)
      (tail : Runs (if Nat.Prime (a + b) then n - 1 else n) b (a + b) r) :
      Runs n a b r

/-- A finite observer, not a bound on `prime_fib`. -/
def observe : Nat → Int → Nat → Nat → Option Nat
  | 0, _, _, _ => none
  | fuel + 1, n, a, b =>
    let c := a + b
    let next := if Nat.Prime c then n - 1 else n
    if next = 0 then some c else observe fuel next b c

open Lean.Order in
theorem search_sound : ∀ n a b r, search n a b = some r → Runs n a b r := by
  apply search.fixpoint_induct (motive := fun f => ∀ n a b r, f n a b = some r → Runs n a b r)
  · exact admissible_pi_apply _ (fun n => admissible_pi_apply _ (fun a =>
      admissible_pi_apply _ (fun b => admissible_pi _ (fun r =>
        Option.admissible_eq_some _ r))))
  · intro f ih n a b r h
    dsimp only at h
    by_cases hs : (if Nat.Prime (a + b) then n - 1 else n) = 0
    · rw [if_pos hs] at h
      cases Option.some.inj h
      exact Runs.done n a b hs
    · rw [if_neg hs] at h
      exact Runs.step hs (ih _ _ _ _ h)

theorem search_complete {n a b r} (h : Runs n a b r) : search n a b = some r := by
  induction h with
  | done n a b stop => rw [search.eq_1, if_pos stop]
  | step cont tail ih => rw [search.eq_1, if_neg cont]; exact ih

theorem search_iff_runs {n a b r} : search n a b = some r ↔ Runs n a b r :=
  ⟨search_sound n a b r, search_complete⟩

theorem runs_nonnegative {n a b r} (h : Runs n a b r) : 0 ≤ n := by
  induction h with
  | done n a b stop => split at stop <;> omega
  | step cont tail ih => split at ih <;> omega

theorem runs_rank {n a b r} (h : Runs n a b r) :
    ∀ k, a = Nat.fib k → b = Nat.fib (k + 1) → 0 < n →
    ∃ j, k + 2 ≤ j ∧ r = Nat.fib j ∧ Nat.Prime r ∧
      (primeCount (j + 1) : Int) = n + primeCount (k + 2) := by
  induction h with
  | done n a b stop =>
    intro k ha hb hn
    have hf : a + b = Nat.fib (k + 2) := by rw [ha, hb, Nat.fib_add_two]
    have hp : Nat.Prime (a + b) := by
      by_contra hp
      simp only [hp, ↓reduceIte] at stop
      omega
    have hn1 : n = 1 := by simp only [hp, ↓reduceIte] at stop; omega
    refine ⟨k + 2, le_rfl, hf, hp, ?_⟩
    simp [primeCount, ← hf, hp, hn1]
    omega
  | @step n a b r cont tail ih =>
    intro k ha hb hn
    have hf : a + b = Nat.fib (k + 2) := by rw [ha, hb, Nat.fib_add_two]
    have hn' : 0 < (if Nat.Prime (a + b) then n - 1 else n) := by
      split <;> split at cont <;> omega
    obtain ⟨j, hj, hr, hp, hc⟩ := ih (k + 1) hb (by simpa [Nat.add_assoc] using hf) hn'
    refine ⟨j, by omega, hr, hp, ?_⟩
    have he : primeCount (k + 1 + 2) = primeCount (k + 2) +
        if Nat.Prime (a + b) then 1 else 0 := by
      rw [hf]
      simpa [Nat.add_assoc] using (show primeCount ((k + 2) + 1) =
        primeCount (k + 2) + (if Nat.Prime (Nat.fib (k + 2)) then 1 else 0) from rfl)
    rw [he] at hc
    split at hc <;> push_cast at hc <;> omega

theorem primeCount_mono : Monotone primeCount := by
  apply monotone_nat_of_le_succ
  intro k
  simp only [primeCount]
  omega

/-- A prime at index `j` is reached after exactly the intervening prime hits.
This theorem supplies termination whenever a finite rank witness exists. -/
theorem rank_runs (d k : Nat) :
    Nat.Prime (Nat.fib (k + d + 2)) →
    Runs ((primeCount (k + d + 3) : Int) - primeCount (k + 2))
      (Nat.fib k) (Nat.fib (k + 1)) (Nat.fib (k + d + 2)) := by
  induction d generalizing k with
  | zero =>
    intro hp
    have hc : primeCount (k + 3) = primeCount (k + 2) + 1 := by
      change primeCount ((k + 2) + 1) = primeCount (k + 2) + 1
      simp only [primeCount, hp, ↓reduceIte]
    have hn : (primeCount (k + 0 + 3) : Int) - primeCount (k + 2) = 1 := by
      simp only [Nat.add_zero, hc, Nat.cast_add, Nat.cast_one]; omega
    rw [hn]
    simpa only [Nat.add_zero, Nat.fib_add_two] using
      Runs.done 1 (Nat.fib k) (Nat.fib (k + 1)) (by
        simpa only [← Nat.fib_add_two, hp, ↓reduceIte] using (show (1 : Int) - 1 = 0 by omega))
  | succ d ih =>
    intro hp
    have hp' : Nat.Prime (Nat.fib ((k + 1) + d + 2)) := by
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp
    have hrec := ih (k + 1) hp'
    have hcount : primeCount (k + 3) = primeCount (k + 2) +
        if Nat.Prime (Nat.fib (k + 2)) then 1 else 0 := by
      simpa only [Nat.add_assoc] using (show primeCount ((k + 2) + 1) =
        primeCount (k + 2) + (if Nat.Prime (Nat.fib (k + 2)) then 1 else 0) from rfl)
    have hlast : primeCount (k + (d + 1) + 3) = primeCount (k + (d + 1) + 2) + 1 := by
      simpa only [Nat.add_assoc] using (show primeCount ((k + (d + 1) + 2) + 1) =
        primeCount (k + (d + 1) + 2) + 1 by simp only [primeCount, hp, ↓reduceIte])
    have hle := primeCount_mono (show k + 3 ≤ k + (d + 1) + 2 by omega)
    have hpos : 0 < (primeCount (k + (d + 1) + 3) : Int) - primeCount (k + 3) := by
      rw [hlast]; push_cast; omega
    have hnext : (if Nat.Prime (Nat.fib k + Nat.fib (k + 1)) then
        (primeCount (k + (d + 1) + 3) : Int) - primeCount (k + 2) - 1
        else (primeCount (k + (d + 1) + 3) : Int) - primeCount (k + 2)) =
        (primeCount ((k + 1) + d + 3) : Int) - primeCount ((k + 1) + 2) := by
      rw [← Nat.fib_add_two]
      have hi : (k + 1) + d + 3 = k + (d + 1) + 3 := by omega
      rw [hi, show (k + 1) + 2 = k + 3 by omega, hcount]
      split
      · push_cast; omega
      · push_cast; omega
    apply Runs.step
    · rw [hnext]
      have hi : (k + 1) + d + 3 = k + (d + 1) + 3 := by omega
      rw [hi, show (k + 1) + 2 = k + 3 by omega]
      omega
    · rw [hnext, ← Nat.fib_add_two]
      convert hrec using 1
      congr 2
      omega

theorem observe_sound {fuel n a b r} (h : observe fuel n a b = some r) :
    Runs n a b r := by
  induction fuel generalizing n a b with
  | zero => simp [observe] at h
  | succ fuel ih =>
    simp only [observe] at h
    by_cases hs : (if Nat.Prime (a + b) then n - 1 else n) = 0
    · rw [if_pos hs] at h
      cases Option.some.inj h
      exact Runs.done n a b hs
    · rw [if_neg hs] at h
      exact Runs.step hs (ih h)

theorem runs_observe {n a b r} (h : Runs n a b r) :
    ∃ fuel, observe fuel n a b = some r := by
  induction h with
  | done n a b hs => exact ⟨1, by simp only [observe, hs, ↓reduceIte]⟩
  | step hs tail ih =>
    obtain ⟨fuel, hf⟩ := ih
    exact ⟨fuel + 1, by simp only [observe, hs, ↓reduceIte, hf]⟩

theorem observe_search_iff (n : Int) (r : Nat) :
    (∃ fuel, observe fuel n 0 1 = some r) ↔ prime_fib n = some r := by
  constructor
  · rintro ⟨fuel, hf⟩
    exact search_complete (observe_sound hf)
  · intro h
    exact runs_observe (search_sound n 0 1 r h)

/-- Exact behavior of the nonpositive exceptional input that does return. -/
def zero_prop : Prop := prime_fib 0 = some 1

theorem zero_thm : zero_prop := by
  unfold zero_prop prime_fib
  rw [search.eq_1]
  norm_num

/-- Negative counters can never reach zero. -/
def negative_prop (n : Int) : Prop := n < 0 → prime_fib n = none

theorem negative_thm (n : Int) : negative_prop n := by
  intro hn
  cases he : prime_fib n with
  | none => rfl
  | some r =>
    have := runs_nonnegative (search_sound n 0 1 r he)
    omega

/-- A positive rank returns exactly the prime at that Fibonacci-prime rank.
Counting indices is unambiguous: the only repeated Fibonacci value is 1,
which is not prime. -/
def rank_prop (n : Int) : Prop :=
  0 < n → ∀ r, prime_fib n = some r ↔
    ∃ k, 2 ≤ k ∧ r = Nat.fib k ∧ Nat.Prime r ∧
      (primeCount (k + 1) : Int) = n

theorem rank_thm (n : Int) : rank_prop n := by
  intro hn r
  constructor
  · intro h
    obtain ⟨k, hk, hr, hp, hc⟩ :=
      runs_rank (search_sound n 0 1 r h) 0 rfl rfl hn
    refine ⟨k, hk, hr, hp, ?_⟩
    simpa [primeCount] using hc
  · rintro ⟨k, hk, hr, hp, hc⟩
    have hi : 0 + (k - 2) + 2 = k := by omega
    have hj : 0 + (k - 2) + 3 = k + 1 := by omega
    have hrun := rank_runs (k - 2) 0 (by simpa only [hi, ← hr] using hp)
    rw [hi, hj, hc] at hrun
    have hrun' : Runs n 0 1 r := by simpa [primeCount, ← hr] using hrun
    exact search_complete hrun'

/-- Positive inputs only return prime numbers. -/
def prime_prop (n : Int) : Prop :=
  0 < n → ∀ r, prime_fib n = some r → Nat.Prime r

theorem prime_thm (n : Int) : prime_prop n := by
  intro hn r hr
  obtain ⟨_, _, _, hp, _⟩ := (rank_thm n hn r).mp hr
  exact hp

/-- Every returned value, including the zero-input value, is Fibonacci. -/
def fibonacci_prop (n : Int) : Prop :=
  ∀ r, prime_fib n = some r → ∃ k, r = Nat.fib k

theorem fibonacci_thm (n : Int) : fibonacci_prop n := by
  intro r hr
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have hnone := negative_thm n hn
    rw [hnone] at hr
    contradiction
  · subst n
    have hzero := zero_thm
    unfold zero_prop at hzero
    rw [hzero] at hr
    exact ⟨1, by simpa using (Option.some.inj hr).symm⟩
  · obtain ⟨k, _, hk, _, _⟩ := (rank_thm n hn r).mp hr
    exact ⟨k, hk⟩

/-- Termination is characterized, not assumed. Proving termination for all
positive ranks would require the open infinitude-of-Fibonacci-primes problem. -/
def termination_prop (n : Int) : Prop :=
  (∃ r, prime_fib n = some r) ↔
    n = 0 ∨ (0 < n ∧ ∃ k, 2 ≤ k ∧ Nat.Prime (Nat.fib k) ∧
      (primeCount (k + 1) : Int) = n)

theorem termination_thm (n : Int) : termination_prop n := by
  constructor
  · rintro ⟨r, hr⟩
    have hn := runs_nonnegative (search_sound n 0 1 r hr)
    by_cases hz : n = 0
    · exact Or.inl hz
    · have hp : 0 < n := by omega
      obtain ⟨k, hk, he, hprime, hc⟩ := (rank_thm n hp r).mp hr
      exact Or.inr ⟨hp, k, hk, he ▸ hprime, hc⟩
  · rintro (hz | ⟨hn, k, hk, hp, hc⟩)
    · subst n
      exact ⟨1, zero_thm⟩
    · exact ⟨Nat.fib k, (rank_thm n hn _).mpr ⟨k, hk, rfl, hp, hc⟩⟩

/-- The full partial-function contract, on all integer inputs. -/
def Post_prop (n : Int) : Prop :=
  zero_prop ∧ negative_prop n ∧ prime_prop n ∧ fibonacci_prop n ∧
    rank_prop n ∧ termination_prop n

/-! ## Property-based tests

These exhaust finite sample spaces, rather than using tests as proofs.
The positive samples include rank 11, beyond the supplied unit tests.
Unbounded divergence is not an executable decision procedure. For
`negative_prop`, and the divergent side of `termination_prop` / `Post_prop`,
we instead test finite observations. `observe_search_iff` proves the
connection of this executable layer to the unbounded implementation.
The theorem domains above are not restricted to these test bounds.
-/

/-- The finite rank witnesses used only by the tests (indices 0 through 47). -/
def testRanks : List (Nat × Nat) :=
  (List.range 48).filterMap fun k =>
    if Nat.Prime (Nat.fib k) then some (Nat.fib k, primeCount (k + 1)) else none

/-- Executable primality check on a returning positive sample. -/
def checkPrime (n : Nat) : Bool :=
  n == 0 || (prime_fib n).any (fun r => decide (Nat.Prime r))

/-- Executable Fibonacci-membership check on the sample space. -/
def checkFibonacci (n : Nat) : Bool :=
  (prime_fib n).any (fun r => (List.range 48).any (fun k => r == Nat.fib k))

/-- Check both directions of the exact-rank property on generated candidates. -/
def checkRank (n : Nat) : Bool :=
  if n = 0 then true else
    let result := prime_fib n
    let witnesses := testRanks
    let candidates := (List.range 48).map Nat.fib ++ List.range 100
    result.isSome &&
      result.any (fun r => witnesses.any (fun p => p.1 == r && p.2 == n)) &&
      candidates.all (fun r =>
        (result == some r) == witnesses.any (fun p => p.1 == r && p.2 == n))

/-- Executable termination equivalence on samples with finite witnesses. -/
def checkTermination (n : Nat) : Bool :=
  (prime_fib n).isSome == (n == 0 || testRanks.any (fun p => p.2 == n))

/-- PBT for `zero_prop`: every nonempty observation agrees with the zero return. -/
example : (List.range 48).all (fun fuel =>
    observe (fuel + 1) 0 0 1 == prime_fib 0) = true := by native_decide

-- PBT: `negative_prop` has no terminating unbounded evaluator at negative
-- inputs. Test its finite-observation counterpart for 960 input/fuel pairs.
example : (List.range 20).all (fun n => (List.range 48).all (fun fuel =>
    observe fuel (-(Int.ofNat n + 1)) 0 1 == none)) = true := by native_decide

-- PBT for `prime_prop`.
example : (List.range 12).all checkPrime = true := by native_decide

-- PBT for `fibonacci_prop`.
example : (List.range 12).all checkFibonacci = true := by native_decide

-- PBT for `rank_prop`, including both directions on generated candidate values.
example : (List.range 12).all checkRank = true := by native_decide

-- PBT for `termination_prop` on witnessed ranks.
example : (List.range 12).all checkTermination = true := by native_decide

-- PBT for the conjunction `Post_prop`, on terminating samples and negative
-- finite observations. None of these sample bounds occur in the specification.
example : (List.range 12).all (fun n =>
    (prime_fib 0 == some 1) && checkPrime n && checkFibonacci n &&
    checkRank n && checkTermination n &&
    (List.range 48).all (fun fuel =>
      observe fuel (-(Int.ofNat n + 1)) 0 1 == none)) = true := by native_decide

#eval (List.range 12).all (fun n =>
  checkPrime n && checkFibonacci n && checkRank n && checkTermination n)

/-- Kernel-checked correctness over the entire integer domain. -/
theorem correctness_thm (n : Int) : Pre n → Post_prop n := by
  intro _
  exact ⟨zero_thm, negative_thm n, prime_thm n, fibonacci_thm n,
    rank_thm n, termination_thm n⟩

/-! ## Imperative implementation

The mutable state is the two-element sliding window of the Python list,
plus the remaining integer counter. Tail recursion implements the unbounded
loop; no artificial fuel limit is imposed on either implementation.
-/

/-- An imperative loop iteration with mutable state, in the `Id` monad. -/
def searchImperative (n : Int) (a b : Nat) : Option Nat := Id.run do
  let mut remaining := n
  let mut previous := a
  let mut current := b
  let appended := previous + current
  previous := current
  current := appended
  if Nat.Prime current then
    remaining := remaining - 1
  if remaining = 0 then
    return some current
  else
    return searchImperative remaining previous current
partial_fixpoint monotonicity by
  intro f g hfg n a b
  dsimp only [Id.run, pure, bind]
  split <;> split
  all_goals first | exact Lean.Order.PartialOrder.rel_refl | exact hfg _ _ _

def prime_fib_imperative (n : Int) : Option Nat := searchImperative n 0 1

example : prime_fib_imperative 0 = some 1 := by native_decide
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
example : (List.range 12).all (fun n =>
    prime_fib n == prime_fib_imperative n) = true := by native_decide
#eval (List.range 11).map (fun n => prime_fib_imperative n)

theorem search_equivalence_thm (n : Int) (a b : Nat) :
    search n a b = searchImperative n a b := by
  let F := fun (f : Int → Nat → Nat → Option Nat) (n : Int) (a b : Nat) =>
    let next := if Nat.Prime (a + b) then n - 1 else n
    if next = 0 then some (a + b) else f next b (a + b)
  let G := fun (f : Int → Nat → Nat → Option Nat) (n : Int) (a b : Nat) =>
    if Nat.Prime (a + b) then
      if n - 1 = 0 then some (a + b) else f (n - 1) b (a + b)
    else
      if n = 0 then some (a + b) else f n b (a + b)
  have he : F = G := by
    funext f n a b
    dsimp only [F, G]
    split <;> rfl
  delta search searchImperative
  change Lean.Order.fix F _ n a b = Lean.Order.fix G _ n a b
  congr! 1

/-- Equality includes the least-fixpoint meaning of nontermination. -/
theorem equivalence_thm (n : Int) : prime_fib n = prime_fib_imperative n := by
  exact search_equivalence_thm n 0 1

end humaneval_39_prime_fib
