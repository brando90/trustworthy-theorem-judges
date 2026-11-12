import Mathlib

/-!
# Primality by trial division

Translation of the Python `is_prime` function. Integer inputs are represented by
`Int`, and `Except String Bool` represents either a returned Boolean or the
`ValueError` with its original message. The input type enforces `isinstance(n, int)`.

This discrete mathematical model uses `Nat.sqrt` for the exact integer square-root
cutoff intended by `int(math.sqrt(n))`. The functional and imperative algorithms
both check 2 and 3 first, then the pairs `6*k + 5`, `6*k + 7`. The second member
of a pair is checked even when it exceeds the square-root cutoff, as in Python.
-/

namespace IsPrime23

deriving instance DecidableEq for Except

def errorMessage : String := "Input must be non-negative integer"

/-- One iteration of the source's `6k ± 1` trial division. -/
def pairPasses (n k : Nat) : Bool :=
  n % (6 * k + 5) != 0 && n % (6 * k + 7) != 0

/-- There are `(sqrt n + 1) / 6` terms in `range(5, sqrt n + 1, 6)`. -/
def trialDivision (n : Nat) : Bool :=
  if n ≤ 1 then false
  else if n ≤ 3 then true
  else if n % 2 == 0 || n % 3 == 0 then false
  else (List.range ((Nat.sqrt n + 1) / 6)).all (pairPasses n)

def isPrime (n : Int) : Except String Bool :=
  if n < 0 then .error errorMessage else .ok (trialDivision n.toNat)

/-- An independent, slower executable specification for the divisor-based PBT. -/
def referencePrime (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range n).all (fun d => decide (2 ≤ d → n % d ≠ 0))

-- Unit tests, including both members of a trial pair and perfect-square cutoffs.
example : isPrime 7 = .ok true := by native_decide
example : isPrime 0 = .ok false := by native_decide
example : isPrime (-1) = .error errorMessage := by native_decide
example : isPrime 1 = .ok false := by native_decide
example : isPrime 2 = .ok true := by native_decide
example : isPrime 3 = .ok true := by native_decide
example : isPrime 4 = .ok false := by native_decide
example : isPrime 25 = .ok false := by native_decide
example : isPrime 49 = .ok false := by native_decide
example : isPrime 121 = .ok false := by native_decide
example : isPrime 169 = .ok false := by native_decide
example : isPrime 97 = .ok true := by native_decide
example : isPrime 9973 = .ok true := by native_decide
#eval isPrime 7
#eval isPrime 0
#eval isPrime (-1)

/-- Python's precondition; the Lean input type already guarantees integrality. -/
def Pre (n : Int) : Prop := 0 ≤ n

theorem trial_index_iff (n k : Nat) :
    k < (Nat.sqrt n + 1) / 6 ↔ 6 * k + 5 ≤ Nat.sqrt n := by
  omega

theorem pairPasses_iff (n k : Nat) :
    pairPasses n k = true ↔ n % (6 * k + 5) ≠ 0 ∧ n % (6 * k + 7) ≠ 0 := by
  simp [pairPasses]

/-- Excluding multiples of 2 and 3 leaves precisely the residues 1 and 5. -/
theorem remaining_residues (d : Nat) (h2 : d % 2 ≠ 0) (h3 : d % 3 ≠ 0) :
    d % 6 = 1 ∨ d % 6 = 5 := by
  omega

/-- The trial loop rejects every composite after the small-prime checks. -/
theorem prime_of_trials (n : Nat) (hn : 3 < n)
    (h2 : n % 2 ≠ 0) (h3 : n % 3 ≠ 0)
    (hloop : (List.range ((Nat.sqrt n + 1) / 6)).all (pairPasses n) = true) :
    Nat.Prime n := by
  apply Nat.prime_def_le_sqrt.mpr
  refine ⟨by omega, ?_⟩
  intro d hd hbound hdvd
  have hd2 : d % 2 ≠ 0 := by
    intro h
    exact h2 (Nat.mod_eq_zero_of_dvd ((Nat.dvd_of_mod_eq_zero h).trans hdvd))
  have hd3 : d % 3 ≠ 0 := by
    intro h
    exact h3 (Nat.mod_eq_zero_of_dvd ((Nat.dvd_of_mod_eq_zero h).trans hdvd))
  have hall : ∀ k < (Nat.sqrt n + 1) / 6,
      n % (6 * k + 5) ≠ 0 ∧ n % (6 * k + 7) ≠ 0 := by
    simpa only [List.all_eq_true, List.mem_range, pairPasses_iff] using hloop
  rcases remaining_residues d hd2 hd3 with hr | hr
  · have heq : 6 * ((d - 7) / 6) + 7 = d := by omega
    have hk : (d - 7) / 6 < (Nat.sqrt n + 1) / 6 := by omega
    have h := (hall _ hk).2
    rw [heq] at h
    exact h (Nat.mod_eq_zero_of_dvd hdvd)
  · have heq : 6 * (d / 6) + 5 = d := by omega
    have hk : d / 6 < (Nat.sqrt n + 1) / 6 := by omega
    have h := (hall _ hk).1
    rw [heq] at h
    exact h (Nat.mod_eq_zero_of_dvd hdvd)

/-- Every tested divisor is strictly between 1 and a prime input. -/
theorem trials_of_prime (n : Nat) (hp : Nat.Prime n) :
    (List.range ((Nat.sqrt n + 1) / 6)).all (pairPasses n) = true := by
  apply List.all_eq_true.mpr
  intro k hk
  have hi := (trial_index_iff n k).mp (List.mem_range.mp hk)
  have hsq := Nat.le_sqrt.mp hi
  have hleft : 6 * k + 5 < n := by nlinarith
  have hright : 6 * k + 7 < n := by nlinarith
  apply (pairPasses_iff n k).mpr
  constructor
  · intro h
    exact (Nat.prime_def_lt'.mp hp).2 _ (by omega) hleft
      (Nat.dvd_of_mod_eq_zero h)
  · intro h
    exact (Nat.prime_def_lt'.mp hp).2 _ (by omega) hright
      (Nat.dvd_of_mod_eq_zero h)

theorem trialDivision_correct (n : Nat) : trialDivision n = true ↔ Nat.Prime n := by
  unfold trialDivision
  split_ifs with hsmall hthree hdiv
  · simp only [false_iff]
    intro hp
    have := hp.two_le
    omega
  · have hn : n = 2 ∨ n = 3 := by omega
    rcases hn with rfl | rfl <;> simp [Nat.prime_two, Nat.prime_three]
  · simp only [false_iff]
    intro hp
    have h := (Nat.prime_def_lt'.mp hp).2
    have hd : n % 2 = 0 ∨ n % 3 = 0 := by simpa using hdiv
    rcases hd with hd | hd
    · exact h 2 (by omega) (by omega) (Nat.dvd_of_mod_eq_zero hd)
    · exact h 3 (by omega) (by omega) (Nat.dvd_of_mod_eq_zero hd)
  · have hd : n % 2 ≠ 0 ∧ n % 3 ≠ 0 := by simpa using hdiv
    exact ⟨prime_of_trials n (by omega) hd.1 hd.2, trials_of_prime n⟩

/-- An admissible call returns a Boolean successfully. -/
def returns_bool_prop (n : Int) : Prop := ∃ b : Bool, isPrime n = .ok b

theorem returns_bool_thm (n : Int) (h : Pre n) : returns_bool_prop n := by
  exact ⟨trialDivision n.toNat, by simp [isPrime, show ¬n < 0 from not_lt.mpr h]⟩

/-- Invalid negative inputs raise the source's error, with its original message. -/
def negative_input_prop (n : Int) : Prop :=
  n < 0 → isPrime n = .error errorMessage

theorem negative_input_thm (n : Int) : negative_input_prop n := by
  intro h
  simp [isPrime, h]

/-- Zero and one are not prime. -/
def edge_cases_prop (n : Int) : Prop := n ≤ 1 → isPrime n = .ok false

theorem edge_cases_thm (n : Int) (h : Pre n) : edge_cases_prop n := by
  intro hn
  have hnat : n.toNat ≤ 1 := by omega
  simp [isPrime, show ¬n < 0 from not_lt.mpr h, trialDivision, hnat]

def small_primes_prop (n : Int) : Prop :=
  n = 2 ∨ n = 3 → isPrime n = .ok true

theorem small_primes_thm (n : Int) : small_primes_prop n := by
  rintro (rfl | rfl) <;> norm_num [isPrime, trialDivision]

/-- The source's early divisibility tests reject multiples of 2 or 3 above 3. -/
def small_divisors_prop (n : Int) : Prop :=
  3 < n → (n % 2 = 0 ∨ n % 3 = 0) → isPrime n = .ok false

theorem small_divisors_thm (n : Int) : small_divisors_prop n := by
  intro hn hd
  have hnat : 3 < n.toNat := by omega
  have heq : (n.toNat : Int) = n := Int.toNat_of_nonneg (by omega)
  have hd' : n.toNat % 2 = 0 ∨ n.toNat % 3 = 0 := by omega
  have htest : (n.toNat % 2 == 0 || n.toNat % 3 == 0) = true := by simpa using hd'
  simp [isPrime, show ¬n < 0 by omega, trialDivision,
    show ¬n.toNat ≤ 1 by omega, show ¬n.toNat ≤ 3 by omega, htest]

/-- Both soundness and completeness with respect to mathematical primality. -/
def primality_prop (n : Int) : Prop := isPrime n = .ok true ↔ Nat.Prime n.toNat

theorem primality_thm (n : Int) (h : Pre n) : primality_prop n := by
  simpa [primality_prop, isPrime, show ¬n < 0 from not_lt.mpr h]
    using trialDivision_correct n.toNat

/-- False is returned exactly for the nonprime admissible inputs, including 0 and 1. -/
def nonprime_prop (n : Int) : Prop := isPrime n = .ok false ↔ ¬Nat.Prime n.toNat

theorem nonprime_thm (n : Int) (h : Pre n) : nonprime_prop n := by
  have hc := trialDivision_correct n.toNat
  simp only [nonprime_prop, isPrime, show ¬n < 0 from not_lt.mpr h, if_false,
    Except.ok.injEq]
  rw [← hc]
  cases trialDivision n.toNat <;> decide

/-- The source's stated definition in terms of all positive divisors. -/
def divisors_prop (n : Int) : Prop :=
  isPrime n = .ok true ↔
    1 < n ∧ ∀ d : Nat, d ∣ n.toNat → d = 1 ∨ d = n.toNat

theorem divisors_thm (n : Int) (h : Pre n) : divisors_prop n := by
  have hc : isPrime n = .ok true ↔ Nat.Prime n.toNat := primality_thm n h
  rw [divisors_prop, hc, Nat.prime_def]
  have heq : (2 ≤ n.toNat) ↔ 1 < n := by omega
  rw [heq]

/-- Checking every proper divisor is an executable form of the full definition. -/
theorem referencePrime_correct (n : Nat) : referencePrime n = true ↔ Nat.Prime n := by
  simp only [referencePrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Nat.prime_def_lt', Nat.dvd_iff_mod_eq_zero]
  aesop

/-- The admissible-input contract collects every observable property above. -/
def Post_prop (n : Int) : Prop :=
  returns_bool_prop n ∧ negative_input_prop n ∧ edge_cases_prop n ∧
  small_primes_prop n ∧ small_divisors_prop n ∧ primality_prop n ∧
  nonprime_prop n ∧ divisors_prop n

-- Property-based tests. Each named property has its own bounded executable check.
-- Casting a Nat input to Int constructs an input satisfying Pre, without rejection.

-- PBT: returns_bool_prop, on every admissible integer from 0 through 4095.
example : (List.range 4096).all (fun n =>
    decide (isPrime (n : Int) = .ok false ∨ isPrime (n : Int) = .ok true)) = true := by
  native_decide

-- PBT: negative_input_prop, on -1 through -2048.
example : (List.range 2048).all (fun k =>
    decide (isPrime (-((k : Int) + 1)) = .error errorMessage)) = true := by
  native_decide

-- PBT: edge_cases_prop, including every input satisfying its antecedent and Pre.
example : (List.range 256).all (fun n =>
    decide (n ≤ 1 → isPrime (n : Int) = .ok false)) = true := by
  native_decide

-- PBT: small_primes_prop, including both possible inputs satisfying its antecedent.
example : (List.range 256).all (fun n =>
    decide (n = 2 ∨ n = 3 → isPrime (n : Int) = .ok true)) = true := by
  native_decide

-- PBT: small_divisors_prop, checking the source's Int remainder conditions.
example : (List.range 4096).all (fun n =>
    let z : Int := n
    decide (3 < z → (z % 2 = 0 ∨ z % 3 = 0) → isPrime z = .ok false)) = true := by
  native_decide

-- PBT: primality_prop, using Mathlib's executable primality predicate as the oracle.
example : (List.range 4096).all (fun n =>
    decide (isPrime (n : Int) = .ok true ↔ Nat.Prime n)) = true := by
  native_decide

-- PBT: nonprime_prop, including 0, 1, and all composite numbers in this interval.
example : (List.range 4096).all (fun n =>
    decide (isPrime (n : Int) = .ok false ↔ ¬Nat.Prime n)) = true := by
  native_decide

-- PBT: divisors_prop. referencePrime_correct proves that enumerating proper
-- divisors is equivalent to the universal, unbounded divisor characterization.
example : (List.range 4096).all (fun n =>
    decide (isPrime (n : Int) = .ok true ↔ referencePrime n = true)) = true := by
  native_decide

/-- Executable conjunction corresponding to every component of Post_prop. -/
def postCheck (n : Int) : Bool :=
  let r := isPrime n
  decide (r = .ok false ∨ r = .ok true) &&
  decide (n < 0 → r = .error errorMessage) &&
  decide (n ≤ 1 → r = .ok false) &&
  decide (n = 2 ∨ n = 3 → r = .ok true) &&
  decide (3 < n → (n % 2 = 0 ∨ n % 3 = 0) → r = .ok false) &&
  decide (r = .ok true ↔ Nat.Prime n.toNat) &&
  decide (r = .ok false ↔ ¬Nat.Prime n.toNat) &&
  decide (r = .ok true ↔ referencePrime n.toNat = true)

theorem postCheck_iff (n : Int) : postCheck n = true ↔ Post_prop n := by
  have hnat : 2 ≤ n.toNat ↔ 1 < n := by omega
  simp only [postCheck, Bool.and_eq_true, decide_eq_true_eq, Post_prop,
    returns_bool_prop, negative_input_prop, edge_cases_prop, small_primes_prop,
    small_divisors_prop, primality_prop, nonprime_prop, divisors_prop,
    Bool.exists_bool, referencePrime_correct, Nat.prime_def, hnat, and_assoc]

-- PBT: the whole postcondition on 2048 admissible inputs.
example : (List.range 2048).all (fun n => postCheck (n : Int)) = true := by
  native_decide

-- Randomized PBTs complement the bounded checks, with no sampling rejection for Pre.
#eval Plausible.Testable.check (∀ n : Nat, postCheck (n : Int) = true)
#eval Plausible.Testable.check
  (∀ k : Nat, isPrime (-((k : Int) + 1)) = .error errorMessage)

/-- Every admissible input satisfies the complete postcondition. -/
theorem correctness (n : Int) (h : Pre n) : Post_prop n := by
  exact ⟨returns_bool_thm n h, negative_input_thm n, edge_cases_thm n h,
    small_primes_thm n, small_divisors_thm n, primality_thm n h,
    nonprime_thm n h, divisors_thm n h⟩

/-- Mutable loop with the same early exit on a divisor as the Python loop. -/
def trialLoopImperative (n : Nat) (ks : List Nat) (initial : Bool) : Bool := Id.run do
  let mut passes := initial
  for k in ks do
    if !(pairPasses n k) then
      passes := false
      break
  return passes

def isPrimeImperative (n : Int) : Except String Bool := Id.run do
  if n < 0 then
    return .error errorMessage
  let m := n.toNat
  if m ≤ 1 then
    return .ok false
  if m ≤ 3 then
    return .ok true
  if m % 2 == 0 || m % 3 == 0 then
    return .ok false
  return .ok (trialLoopImperative m (List.range ((Nat.sqrt m + 1) / 6)) true)

-- Imperative unit tests and a bounded comparison covering valid and invalid inputs.
example : isPrimeImperative 7 = .ok true := by native_decide
example : isPrimeImperative 0 = .ok false := by native_decide
example : isPrimeImperative (-1) = .error errorMessage := by native_decide
example : isPrimeImperative 1 = .ok false := by native_decide
example : isPrimeImperative 2 = .ok true := by native_decide
example : isPrimeImperative 3 = .ok true := by native_decide
example : isPrimeImperative 4 = .ok false := by native_decide
example : isPrimeImperative 25 = .ok false := by native_decide
example : isPrimeImperative 49 = .ok false := by native_decide
example : isPrimeImperative 121 = .ok false := by native_decide
example : isPrimeImperative 169 = .ok false := by native_decide
example : isPrimeImperative 97 = .ok true := by native_decide
example : isPrimeImperative 9973 = .ok true := by native_decide
#eval isPrimeImperative 7
#eval isPrimeImperative 0
#eval isPrimeImperative (-1)
example : (List.range 4096).all (fun k =>
    let n : Int := (k : Int) - 32
    decide (isPrime n = isPrimeImperative n)) = true := by
  native_decide

/-- Loop invariant: the result is the initial flag conjoined with every pair check. -/
theorem trialLoopImperative_eq (n : Nat) (ks : List Nat) (initial : Bool) :
    trialLoopImperative n ks initial = (initial && ks.all (pairPasses n)) := by
  induction ks generalizing initial with
  | nil => simp [trialLoopImperative]
  | cons k ks ih =>
    cases h : pairPasses n k with
    | false => simp [trialLoopImperative, List.forIn_cons, List.all_cons, h]
    | true =>
      simpa [trialLoopImperative, List.forIn_cons, List.all_cons, h] using ih initial

/-- Equivalence holds for all integers, including the exceptional negative inputs. -/
theorem functional_eq_imperative (n : Int) : isPrime n = isPrimeImperative n := by
  simp only [isPrime, isPrimeImperative, trialDivision, trialLoopImperative_eq, Bool.true_and]
  split_ifs <;> rfl

end IsPrime23
