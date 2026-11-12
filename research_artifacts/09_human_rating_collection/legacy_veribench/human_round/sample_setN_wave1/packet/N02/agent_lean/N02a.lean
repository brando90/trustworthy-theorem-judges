import Mathlib

/-!
# 23_is_prime — Lean 4 formalization of the VeriBench Python task `is_prime`

The Python source provides

* `pre(n)`: the argument must be an `int` with `n >= 0`;
* `is_prime(n)`: trial division by `2` and `3`, then by every number of the form `6k ± 1`
  up to `int(math.sqrt(n))`; it raises `ValueError` when `pre(n)` fails;
* `check(candidate)`: `candidate(7) is True`, `candidate(0) is False` and `candidate(-1)`
  must raise `ValueError`.

## Modelling decisions

* The Python domain is `int` restricted by `n >= 0`.  The core algorithm is modelled on the
  admissible domain `Nat` (`isPrime`), while the interface layer keeps the full `Int` domain:
  `isPrimeInt : Int → Except String Bool` returns `Except.error errMsg` for negative input,
  the exact counterpart of raising `ValueError` (no obligation is dropped: both the
  admissible and the exceptional branch are specified and proved).
* `int(math.sqrt(n))` denotes `⌊√n⌋`.  The mathematical intent is exact integer square root,
  so we model it with `Nat.sqrt`, Mathlib's exact `⌊√n⌋` on `Nat`.  A `Float` model would add
  IEEE-754 rounding behaviour that the Python program does not rely on (and that would only
  make the bound wrong); `Nat.sqrt` is the faithful exact model of the stated intent.
* The specification of the algorithm is `Nat.Prime`, Mathlib's mathematical definition of
  primality.  All properties, the post-condition and the correctness theorem are stated over
  this exact discrete model, which is the right layer for this integer task.
* The imperative version (`isPrimeImp`, `isPrimeIntImp`) uses `Id.run do` with a mutable
  accumulator and a `for` loop over the same iteration indices as Python's
  `range(5, int(math.sqrt(n)) + 1, 6)`; it is proved equivalent to the functional version.
-/

set_option maxHeartbeats 400000

namespace «23_is_prime»

/-! ## 1. Implementation (functional) -/

/-- The message of the `ValueError` raised by the Python program. -/
def errMsg : String := "Input must be non-negative integer"

/-- The Python loop `for i in range(5, int(math.sqrt(n)) + 1, 6)`.

`sixKLoop n i f` performs at most `f` iterations, starting at `i` and stepping by `6`.
It stops with `true` as soon as `i` has passed `Nat.sqrt n` (Python's `int(math.sqrt(n))`,
i.e. the end of the `range`), reports `false` as soon as `i` or `i + 2` divides `n`,
and otherwise continues with `i + 6`.  The fuel argument makes the recursion structural. -/
def sixKLoop (n i : Nat) : Nat → Bool
  | 0 => true
  | f + 1 =>
      if i > Nat.sqrt n then true
      else if n % i = 0 ∨ n % (i + 2) = 0 then false
      else sixKLoop n (i + 6) f

/-- Functional implementation of Python's `is_prime` on its admissible domain
(non-negative integers, modelled by `Nat`). -/
def isPrime (n : Nat) : Bool :=
  if n ≤ 1 then false
  else if n ≤ 3 then true
  else if n % 2 = 0 ∨ n % 3 = 0 then false
  else sixKLoop n 5 (Nat.sqrt n + 1)

/-- The Python interface on the full `int` domain: a negative argument raises `ValueError`. -/
def isPrimeInt (n : Int) : Except String Bool :=
  if n < 0 then Except.error errMsg else Except.ok (isPrime (Int.toNat n))

/-- Observers used by the executable tests (`Except String Bool` has no `DecidableEq`). -/
def isErr : Except String Bool → Bool
  | .error _ => true
  | .ok _ => false

def okVal : Except String Bool → Option Bool
  | .ok b => some b
  | .error _ => none

def isOkTrue : Except String Bool → Bool
  | .ok true => true
  | _ => false

def isOkFalse : Except String Bool → Bool
  | .ok false => true
  | _ => false

/-- The Python `check` function: `candidate(7) is True`, `candidate(0) is False`,
and `candidate(-1)` raises `ValueError`. -/
def check (candidate : Int → Except String Bool) : Bool :=
  isOkTrue (candidate 7) && isOkFalse (candidate 0) && isErr (candidate (-1))

/-! ## 2. Unit tests (the ground examples of the Python docstring and of `check`) -/

#eval isPrime 2
#eval isPrime 4
#eval isPrime 0
#eval isPrime 7
#eval (List.range 30).map isPrime
#eval isOkTrue (isPrimeInt 7)
#eval isOkFalse (isPrimeInt 0)
#eval isErr (isPrimeInt (-1))
#eval check isPrimeInt

example : isPrime 2 = true := by native_decide
example : isPrime 4 = false := by native_decide
example : isPrime 0 = false := by native_decide
example : isPrime 1 = false := by native_decide
example : isPrime 3 = true := by native_decide
example : isPrime 7 = true := by native_decide
example : isPrime 9 = false := by native_decide
example : isPrime 25 = false := by native_decide
example : isPrime 49 = false := by native_decide
example : isPrime 97 = true := by native_decide
example : isPrime 104729 = true := by native_decide
example : isPrime 1000000 = false := by native_decide
example : (List.range 300).map isPrime = (List.range 300).map (fun n => decide (Nat.Prime n)) := by
  native_decide
example : isOkTrue (isPrimeInt 7) = true := by native_decide
example : isOkFalse (isPrimeInt 0) = true := by native_decide
example : isErr (isPrimeInt (-1)) = true := by native_decide
example : okVal (isPrimeInt 13) = some true := by native_decide
example : okVal (isPrimeInt (-3)) = none := by native_decide
example : check isPrimeInt = true := by native_decide

/-! ## 3. Precondition -/

/-- Python's `pre(n)`: the argument is an integer with `n >= 0`.  Integrality is guaranteed by
the Lean type `Int`, so the remaining obligation is non-negativity. -/

def Pre (n : Int) : Prop := 0 ≤ n

/-- The Python `pre` function itself, as an executable Boolean predicate. -/

def preFn (n : Int) : Bool := decide (0 ≤ n)

/-- `preFn` computes exactly the precondition `Pre`. -/

theorem preFn_spec (n : Int) : preFn n = true ↔ Pre n := by
  simp [preFn, Pre]

/-! ## 4. Core lemmas about the `6k ± 1` trial division -/

/-- Two Booleans are equal as soon as they agree on being `true`. -/

theorem Bool_eq_of_true_iff {a b : Bool} (h : (a = true) ↔ (b = true)) : a = b := by
  cases ha : a <;> cases hb : b <;> simp_all

/-- A composite `n ≥ 2` has a prime divisor `p ≤ √n`.  This is the fact that makes trial
division up to `Nat.sqrt n` (= Python's `int(math.sqrt(n))`) complete. -/

theorem exists_prime_dvd_le_sqrt {n : Nat} (h2 : 2 ≤ n) (hnp : ¬ Nat.Prime n) :
    ∃ p, Nat.Prime p ∧ p ∣ n ∧ p ≤ Nat.sqrt n := by
  obtain ⟨m, hm, hm2, hmn⟩ := Nat.exists_dvd_of_not_prime2 h2 hnp
  have hmd : m * (n / m) = n := Nat.mul_div_cancel' hm
  have hpos : 0 < n / m := by
    by_contra h
    have hz : n / m = 0 := Nat.le_zero.mp (Nat.not_lt.mp h)
    have hn : n = 0 := by rw [← hmd, hz]; simp
    omega
  have hne1 : min m (n / m) ≠ 1 := by
    intro h
    rcases le_total m (n / m) with hh | hh
    · have hmin : min m (n / m) = m := min_eq_left hh
      omega
    · have hmin : min m (n / m) = n / m := min_eq_right hh
      have hnm : n / m = 1 := by omega
      have hnm2 : n = m := by rw [← hmd, hnm]; simp
      omega
  have hge1 : 1 ≤ min m (n / m) := le_min (by omega) (by omega)
  have hge2 : 2 ≤ min m (n / m) := by omega
  have hdvd : min m (n / m) ∣ n := by
    rcases le_total m (n / m) with hh | hh
    · rw [min_eq_left hh]; exact hm
    · rw [min_eq_right hh]; exact Nat.div_dvd_of_dvd hm
  have hsq : min m (n / m) * min m (n / m) ≤ n :=
    (Nat.mul_le_mul (min_le_left _ _) (min_le_right _ _)).trans (le_of_eq hmd)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne1
  exact ⟨p, hp, dvd_trans hpd hdvd,
    (Nat.le_of_dvd (by omega : 0 < min m (n / m)) hpd).trans (Nat.le_sqrt.mpr hsq)⟩

/-- Exact characterisation of one run of the loop: it returns `true` iff none of the pairs
`(i + 6j, i + 6j + 2)` that the Python `range` visits divides `n`. -/

theorem sixKLoop_true_iff (n i f : Nat) :
    sixKLoop n i f = true ↔
      ∀ j < f, i + 6 * j ≤ Nat.sqrt n → ¬(n % (i + 6 * j) = 0 ∨ n % (i + 6 * j + 2) = 0) := by
  induction f generalizing i with
  | zero => simp [sixKLoop]
  | succ f ih =>
      have heq : sixKLoop n i (f + 1) =
          (if i > Nat.sqrt n then true
           else if n % i = 0 ∨ n % (i + 2) = 0 then false
           else sixKLoop n (i + 6) f) := rfl
      rw [heq]
      split
      · rename_i hgt
        constructor
        · intro _ j _ hjl
          exfalso
          omega
        · intro _; rfl
      · split
        · rename_i hle hd
          constructor
          · intro hh; cases hh
          · intro h
            exfalso
            have h0 := h 0 (Nat.zero_lt_succ f) (by omega)
            simp only [Nat.mul_zero, Nat.add_zero] at h0
            exact h0 hd
        · rename_i hle hd
          have ih' := ih (i + 6)
          constructor
          · intro h j hj
            cases j with
            | zero =>
                intro _
                simp only [Nat.mul_zero, Nat.add_zero]
                exact hd
            | succ j =>
                intro hjl
                have h1 : i + 6 * (j + 1) = (i + 6) + 6 * j := by omega
                have h2 := (ih'.mp h) j (by omega) (by omega)
                rw [h1]
                exact h2
          · intro h
            apply ih'.mpr
            intro j hj hjl
            have h1 : i + 6 * (j + 1) = (i + 6) + 6 * j := by omega
            have h2 := h (j + 1) (by omega) (by omega)
            rw [h1] at h2
            exact h2

/-- If the loop reports `true`, no number congruent to `±1` modulo `6` in the scanned window
divides `n`. -/

theorem sixKLoop_true_imp_nodvd {n i f : Nat} (hm : i % 6 = 5) (h : sixKLoop n i f = true) :
    ∀ d, i ≤ d → d < i + 6 * f → d ≤ Nat.sqrt n → (d % 6 = 5 ∨ d % 6 = 1) → ¬ d ∣ n := by
  have key := (sixKLoop_true_iff n i f).mp h
  intro d hd1 hd2 hd3 hd4 hdvd
  have hd0 : d ≠ 0 := by
    have : i ≥ 5 := by omega
    omega
  have hmod : n % d ≠ 0 := by
    rcases hd4 with h5 | h1
    · have h6 : (d - i) % 6 = 0 := by omega
      obtain ⟨j, hj⟩ := Nat.dvd_of_mod_eq_zero h6
      have hjf : j < f := by omega
      have hle : i + 6 * j ≤ Nat.sqrt n := by omega
      have hk := key j hjf hle
      have hj0 : i + 6 * j = d := by omega
      rw [hj0] at hk
      exact fun hh => hk (Or.inl hh)
    · have hge : i + 2 ≤ d := by omega
      have h6 : (d - i - 2) % 6 = 0 := by omega
      obtain ⟨j, hj⟩ := Nat.dvd_of_mod_eq_zero h6
      have hjf : j < f := by omega
      have hle : i + 6 * j ≤ Nat.sqrt n := by omega
      have hk := key j hjf hle
      have hj0 : i + 6 * j + 2 = d := by omega
      rw [hj0] at hk
      exact fun hh => hk (Or.inr hh)
  exact absurd (Nat.mod_eq_zero_of_dvd hdvd) hmod

/-- For a genuine prime the loop never finds a divisor, whatever the fuel is. -/

theorem sixKLoop_eq_true_of_prime {n : Nat} (hp : Nat.Prime n) :
    ∀ f i, 5 ≤ i → i % 6 = 5 → sixKLoop n i f = true := by
  intro f
  induction f with
  | zero => intro _ _ _; rfl
  | succ f ih =>
      intro i hi hm
      have heq : sixKLoop n i (f + 1) =
          (if i > Nat.sqrt n then true
           else if n % i = 0 ∨ n % (i + 2) = 0 then false
           else sixKLoop n (i + 6) f) := rfl
      rw [heq]
      split
      · rfl
      · rename_i hle
        have hsq : i * i ≤ n := Nat.le_sqrt.mp (by omega : i ≤ Nat.sqrt n)
        split
        · rename_i hd
          exfalso
          rcases hd with hd | hd
          · have hdiv : i ∣ n := Nat.dvd_of_mod_eq_zero hd
            rcases Nat.Prime.eq_one_or_self_of_dvd hp i hdiv with h1 | h2
            · omega
            · subst h2
              nlinarith [hp.two_le]
          · have hdiv : i + 2 ∣ n := Nat.dvd_of_mod_eq_zero hd
            rcases Nat.Prime.eq_one_or_self_of_dvd hp (i + 2) hdiv with h1 | h2
            · omega
            · subst h2
              nlinarith
        · exact ih (i + 6) (by omega) (by omega)

/-! ## 5. The specification theorem for the functional implementation -/

/-- `isPrime` decides `Nat.Prime` exactly, on the whole admissible domain `Nat`. -/

theorem isPrime_iff_prime (n : Nat) : isPrime n = true ↔ Nat.Prime n := by
  rw [isPrime]
  split
  · rename_i h1
    constructor
    · intro hh; cases hh
    · intro hp; exfalso; have := hp.two_le; omega
  · split
    · rename_i h1 h2
      constructor
      · intro _
        have h : n = 2 ∨ n = 3 := by omega
        rcases h with rfl | rfl <;> decide
      · intro _; rfl
    · split
      · rename_i h1 h2 hd
        constructor
        · intro hh; cases hh
        · intro hp
          exfalso
          have := hp.two_le
          rcases hd with hd2 | hd3
          · have h := Nat.Prime.eq_one_or_self_of_dvd hp 2 (Nat.dvd_of_mod_eq_zero hd2)
            omega
          · have h := Nat.Prime.eq_one_or_self_of_dvd hp 3 (Nat.dvd_of_mod_eq_zero hd3)
            omega
      · rename_i h1 h2 hd
        constructor
        · intro hloop
          by_contra hnp
          obtain ⟨p, hp, hpd, hps⟩ := exists_prime_dvd_le_sqrt (by omega) hnp
          have h2 : n % 2 ≠ 0 := fun h => hd (Or.inl h)
          have h3 : n % 3 ≠ 0 := fun h => hd (Or.inr h)
          have hp2 : p ≠ 2 := by
            rintro rfl
            exact h2 (Nat.mod_eq_zero_of_dvd hpd)
          have hp3 : p ≠ 3 := by
            rintro rfl
            exact h3 (Nat.mod_eq_zero_of_dvd hpd)
          have hodd : p % 2 = 1 := by
            rcases hp.eq_two_or_odd with h | h
            · exact absurd h hp2
            · exact h
          have hmod : p % 6 = 5 ∨ p % 6 = 1 := by
            have hl : p % 6 < 6 := Nat.mod_lt p (by decide)
            have h3' : p % 6 % 3 = p % 3 := Nat.mod_mod_of_dvd p (by decide : 3 ∣ 6)
            have h2' : p % 6 % 2 = p % 2 := Nat.mod_mod_of_dvd p (by decide : 2 ∣ 6)
            have h3'' : p % 3 ≠ 0 := by
              intro hh
              have hd3 : 3 ∣ p := Nat.dvd_of_mod_eq_zero hh
              exact hp3 ((Nat.Prime.dvd_iff_eq hp (by decide : (3 : Nat) ≠ 1)).mp hd3)
            omega
          have hp5 : 5 ≤ p := by
            have := hp.two_le
            omega
          have hcontra :=
            sixKLoop_true_imp_nodvd (by decide : (5 : Nat) % 6 = 5) hloop p hp5 (by omega) hps hmod
          exact hcontra hpd
        · intro hp
          exact sixKLoop_eq_true_of_prime hp (Nat.sqrt n + 1) 5 (by omega) (by decide)

/-- The same statement in `decide` form. -/

theorem isPrime_eq_decide (n : Nat) : isPrime n = decide (Nat.Prime n) := by
  apply Bool_eq_of_true_iff
  rw [decide_eq_true_iff, isPrime_iff_prime]

/-- And in the negative form. -/

theorem isPrime_eq_false_iff (n : Nat) : isPrime n = false ↔ ¬ Nat.Prime n := by
  rw [isPrime_eq_decide, decide_eq_false_iff_not]

/-- Behaviour of the `Int` interface on admissible input. -/

theorem isPrimeInt_of_nonneg {n : Int} (h : 0 ≤ n) :
    isPrimeInt n = Except.ok (isPrime (Int.toNat n)) := by
  rw [isPrimeInt, if_neg (by omega : ¬(n < 0))]

/-- Behaviour of the `Int` interface on a precondition violation (Python's `ValueError`). -/

theorem isPrimeInt_of_neg {n : Int} (h : n < 0) :
    isPrimeInt n = Except.error errMsg := by
  rw [isPrimeInt, if_pos h]

/-! ## 6. Properties of the program, as propositions, with proofs -/

/-- `is_prime(n) is True` exactly for prime `n`. -/

def prime_spec_prop : Prop := ∀ n : Nat, isPrime n = true ↔ Nat.Prime n

theorem prime_spec_thm : prime_spec_prop := fun n => isPrime_iff_prime n

/-- `is_prime(n) is False` exactly for composite (or tiny) `n`. -/

def not_prime_spec_prop : Prop := ∀ n : Nat, isPrime n = false ↔ ¬ Nat.Prime n

theorem not_prime_spec_thm : not_prime_spec_prop := fun n => isPrime_eq_false_iff n

/-- The implementation is the decision procedure for `Nat.Prime`. -/

def decide_spec_prop : Prop := ∀ n : Nat, isPrime n = decide (Nat.Prime n)

theorem decide_spec_thm : decide_spec_prop := fun n => isPrime_eq_decide n

/-- `0` and `1` are not prime (Python: `if n <= 1: return False`). -/

def small_prop : Prop := ∀ n : Nat, n < 2 → isPrime n = false

theorem small_thm : small_prop := by
  intro n hn
  have h : n ≤ 1 := by omega
  simp [isPrime, h]

/-- `2` and `3` are prime (Python: `if n <= 3: return True`). -/

def two_three_prop : Prop := isPrime 2 = true ∧ isPrime 3 = true

theorem two_three_thm : two_three_prop := ⟨rfl, rfl⟩

/-- The `n % 2 == 0 or n % 3 == 0` shortcut of the Python program. -/

def div23_prop : Prop := ∀ n : Nat, 4 ≤ n → (n % 2 = 0 ∨ n % 3 = 0) → isPrime n = false

theorem div23_thm : div23_prop := by
  intro n h4 h3
  have hn1 : ¬(n ≤ 1) := by omega
  have hn3 : ¬(n ≤ 3) := by omega
  simp [isPrime, hn1, hn3, h3]

/-- Trial division up to `⌊√n⌋` characterises primality: the mathematical content of the
Python loop bound `int(math.sqrt(n))`. -/

def trial_div_prop : Prop :=
  ∀ n : Nat, 2 ≤ n → (isPrime n = true ↔ ∀ d, 2 ≤ d → d ≤ Nat.sqrt n → ¬ d ∣ n)

theorem trial_div_thm : trial_div_prop := by
  intro n h2
  rw [isPrime_iff_prime]
  constructor
  · intro hp d hd2 hds hdd
    rcases Nat.Prime.eq_one_or_self_of_dvd hp d hdd with h | h
    · omega
    · rw [h] at hds
      have : n * n ≤ n := Nat.le_sqrt.mp hds
      nlinarith [hp.two_le]
  · intro h
    by_contra hnp
    obtain ⟨p, hp, hpd, hps⟩ := exists_prime_dvd_le_sqrt h2 hnp
    exact h p hp.two_le hps hpd

/-- A precondition violation raises `ValueError`. -/

def error_prop : Prop := ∀ n : Int, n < 0 → ∃ msg : String, isPrimeInt n = Except.error msg

theorem error_thm : error_prop := fun _ hn => ⟨errMsg, isPrimeInt_of_neg hn⟩

/-- On admissible input the call succeeds and the returned flag is correct. -/

def ok_prop : Prop :=
  ∀ n : Int, Pre n → ∃ b : Bool, isPrimeInt n = Except.ok b ∧ (b = true ↔ Nat.Prime (Int.toNat n))

theorem ok_thm : ok_prop := by
  intro n hn
  exact ⟨isPrime (Int.toNat n), isPrimeInt_of_nonneg hn, isPrime_iff_prime (Int.toNat n)⟩

/-- The Python `check` function accepts our candidate. -/

def check_prop : Prop := check isPrimeInt = true

theorem check_thm : check_prop := by
  show check isPrimeInt = true
  decide

/-! ## 7. Post-condition -/

/-- Post-condition of the Python `is_prime`: on admissible input the returned flag is `true`
exactly for primes; on a precondition violation the `ValueError` result is returned. -/

def Post_prop (n : Int) (r : Except String Bool) : Prop :=
  (Pre n → ∃ b : Bool, r = Except.ok b ∧ (b = true ↔ Nat.Prime (Int.toNat n))) ∧
  (¬ Pre n → ∃ msg : String, r = Except.error msg)

/-- Executable counterpart of `Post_prop`, used by the property-based tests below
(`Post_prop` quantifies over `String`, so it is tested through this Boolean form). -/

def postCheck (n : Int) : Bool :=
  match isPrimeInt n with
  | .ok b => decide (0 ≤ n) && decide (b = true ↔ Nat.Prime (Int.toNat n))
  | .error _ => decide (n < 0)

/-- The executable post-condition check really does check `Post_prop`. -/

theorem postCheck_sound (n : Int) : postCheck n = true → Post_prop n (isPrimeInt n) := by
  intro h
  cases hr : isPrimeInt n with
  | ok b =>
      simp only [postCheck, hr] at h
      have hand := (Bool.and_eq_true _ _).mp h
      have h0 : 0 ≤ n := decide_eq_true_iff.mp hand.1
      have hb : (b = true ↔ Nat.Prime (Int.toNat n)) := decide_eq_true_iff.mp hand.2
      exact ⟨fun _ => ⟨b, rfl, hb⟩, fun hn => absurd h0 hn⟩
  | error msg =>
      simp only [postCheck, hr] at h
      have hn : n < 0 := decide_eq_true_iff.mp h
      exact ⟨fun h0 => absurd h0 (by intro hh; have : 0 ≤ n := hh; omega), fun _ => ⟨msg, rfl⟩⟩

/-! ## 8. Property-based tests -/

-- PBT for `prime_spec_prop` (executable Boolean form of the specification)
example : (List.range 500).all (fun n => isPrime n == decide (Nat.Prime n)) = true := by native_decide
#eval Plausible.Testable.check (∀ n : Nat, isPrime (n % 300) = decide (Nat.Prime (n % 300)))
#eval Plausible.Testable.check (∀ n : Nat, isPrime n = decide (Nat.Prime n))

-- PBT for `not_prime_spec_prop`
example : (List.range 500).all (fun n => decide (isPrime n = false ↔ ¬ Nat.Prime n)) = true := by
  native_decide
#eval Plausible.Testable.check
  (∀ n : Nat, (isPrime (n % 300) = false) = !decide (Nat.Prime (n % 300)))

-- PBT for `decide_spec_prop`
example : (List.range 500).all (fun n => decide (isPrime n = decide (Nat.Prime n))) = true := by
  native_decide

-- PBT for `small_prop`
example : (List.range 2).all (fun n => isPrime n = false) = true := by native_decide
#eval Plausible.Testable.check (∀ n : Nat, isPrime (n % 2) = false)

-- PBT for `two_three_prop`
example : ((isPrime 2 = true) && (isPrime 3 = true)) = true := by native_decide

-- PBT for `div23_prop`
example : (List.range 400).all
    (fun n => decide (4 ≤ n → (n % 2 = 0 ∨ n % 3 = 0) → isPrime n = false)) = true := by native_decide
#eval Plausible.Testable.check
  (∀ n : Nat,
    decide (4 ≤ n % 300 → ((n % 300) % 2 = 0 ∨ (n % 300) % 3 = 0) → isPrime (n % 300) = false) = true)

-- PBT for `trial_div_prop`
example : (List.range 400).all
    (fun n => decide (2 ≤ n →
      (isPrime n = true ↔
        (List.range (Nat.sqrt n + 1)).all (fun d => decide (2 ≤ d → ¬ d ∣ n))))) = true := by
  native_decide

-- PBT for `error_prop`
example : (List.range 100).all (fun k => isErr (isPrimeInt (-(k : Int) - 1))) = true := by native_decide
#eval Plausible.Testable.check (∀ n : Nat, isErr (isPrimeInt (-(n : Int) - 1)) = true)

-- PBT for `ok_prop`
example : (List.range 300).all (fun k => okVal (isPrimeInt k) == some (decide (Nat.Prime k))) = true := by
  native_decide
#eval Plausible.Testable.check
  (∀ n : Nat, okVal (isPrimeInt (n % 300)) == some (decide (Nat.Prime (n % 300))))

-- PBT for `preFn_spec` (the Python `pre` function)
example : (List.range 60).all (fun k => preFn k && !preFn (-(k : Int) - 1)) = true := by native_decide
#eval Plausible.Testable.check (∀ n : Nat, (preFn n && !preFn (-(n : Int) - 1)) = true)

-- PBT for `check_prop`
example : check isPrimeInt = true := by decide
#eval check isPrimeInt

-- PBT for `Post_prop`, through its executable counterpart `postCheck`
example : (List.range 200).all (fun k => postCheck k && postCheck (-(k : Int) - 1)) = true := by
  native_decide
#eval Plausible.Testable.check (∀ n : Nat, (postCheck (n % 200) && postCheck (-(n : Int) - 1)) = true)

/-! ## 9. Correctness: `Pre → Post` -/

/-- Main correctness theorem: whenever the Python precondition holds, the result of the
program satisfies the post-condition. -/

theorem correctness_thm (n : Int) (h : Pre n) : Post_prop n (isPrimeInt n) := by
  have h0 : 0 ≤ n := h
  have hr : isPrimeInt n = Except.ok (isPrime (Int.toNat n)) := isPrimeInt_of_nonneg h0
  exact ⟨fun _ => ⟨isPrime (Int.toNat n), hr, isPrime_iff_prime (Int.toNat n)⟩,
    fun hn => absurd h hn⟩

/-- The precondition-violating branch also satisfies the post-condition: it raises the error. -/

theorem correctness_neg_thm (n : Int) (h : ¬ Pre n) : Post_prop n (isPrimeInt n) := by
  have hn : n < 0 := by
    have hz : ¬(0 ≤ n) := h
    omega
  have hr : isPrimeInt n = Except.error errMsg := isPrimeInt_of_neg hn
  exact ⟨fun h0 => absurd h0 h, fun _ => ⟨errMsg, hr⟩⟩

/-! ## 10. Imperative implementation (`Id.run do` with mutable state) -/

/-- The imperative trial-division loop: a `for` loop over the iteration index with a mutable
accumulator `res`.  Iteration `k` corresponds to Python's loop variable `i = 5 + 6 * k`, and
the guard `5 + 6 * k ≤ Nat.sqrt n` is Python's `range` bound `i < int(math.sqrt(n)) + 1`.
The loop body checks `n % i == 0 or n % (i + 2) == 0`, exactly as the Python body does. -/

def isPrimeImpLoop (n : Nat) : Bool := Id.run do
  let mut res := true
  for k in List.range (Nat.sqrt n + 1) do
    if 5 + 6 * k ≤ Nat.sqrt n ∧ (n % (5 + 6 * k) = 0 ∨ n % (5 + 6 * k + 2) = 0) then
      res := false
  return res

/-- Imperative counterpart of `isPrime`. -/

def isPrimeImp (n : Nat) : Bool := Id.run do
  if n ≤ 1 then return false
  if n ≤ 3 then return true
  if n % 2 = 0 ∨ n % 3 = 0 then return false
  return isPrimeImpLoop n

/-- Imperative counterpart of `isPrimeInt`, including the `ValueError` branch. -/

def isPrimeIntImp (n : Int) : Except String Bool := Id.run do
  if n < 0 then return Except.error errMsg
  let m := Int.toNat n
  let mut res := isPrimeImp m
  return Except.ok res

/-! ## 11. Imperative tests -/

#eval isPrimeImp 7
#eval (List.range 30).map isPrimeImp
#eval isErr (isPrimeIntImp (-1))
#eval okVal (isPrimeIntImp 7)
#eval check (fun n => isPrimeIntImp n)

example : isPrimeImp 0 = false := by native_decide
example : isPrimeImp 1 = false := by native_decide
example : isPrimeImp 2 = true := by native_decide
example : isPrimeImp 4 = false := by native_decide
example : isPrimeImp 7 = true := by native_decide
example : isPrimeImp 97 = true := by native_decide
example : isPrimeImp 104729 = true := by native_decide
example : (List.range 400).all (fun n => isPrimeImp n == isPrime n) = true := by native_decide
example : (List.range 400).all (fun n => isPrimeImp n == decide (Nat.Prime n)) = true := by
  native_decide
example : isErr (isPrimeIntImp (-1)) = true := by native_decide
example : okVal (isPrimeIntImp 13) = some true := by native_decide
example : (List.range 200).all (fun k => okVal (isPrimeIntImp k) == okVal (isPrimeInt k)) = true := by
  native_decide
example : (List.range 50).all (fun k => isErr (isPrimeIntImp (-(k : Int) - 1))) = true := by
  native_decide
example : check (fun n => isPrimeIntImp n) = true := by native_decide

/-! ## 12. Equivalence: functional = imperative -/

/-- The `for` loop with the mutable accumulator computes the conjunction of the
per-iteration checks. -/

theorem forIn_loop_eq (n : Nat) :
    ∀ (ks : List Nat) (b : Bool),
      (forIn ks b (fun k r =>
          if 5 + 6 * k ≤ Nat.sqrt n ∧ (n % (5 + 6 * k) = 0 ∨ n % (5 + 6 * k + 2) = 0)
            then pure (ForInStep.yield false) else pure (ForInStep.yield r)) : Id Bool)
        = pure (b && ks.all
            (fun k =>
              decide (¬(5 + 6 * k ≤ Nat.sqrt n ∧ (n % (5 + 6 * k) = 0 ∨ n % (5 + 6 * k + 2) = 0))))) := by
  intro ks
  induction ks with
  | nil => intro b; simp [List.forIn_nil]
  | cons x xs ih =>
      intro b
      simp only [List.forIn_cons, List.all_cons]
      split
      · rename_i h
        simp [ih, h]
      · rename_i h
        simp [ih, h]

set_option linter.deprecated false in
theorem isPrimeImpLoop_eq (n : Nat) :
    isPrimeImpLoop n = (List.range (Nat.sqrt n + 1)).all
        (fun k =>
          decide (¬(5 + 6 * k ≤ Nat.sqrt n ∧ (n % (5 + 6 * k) = 0 ∨ n % (5 + 6 * k + 2) = 0)))) := by
  have h := forIn_loop_eq n (List.range (Nat.sqrt n + 1)) true
  simp only [isPrimeImpLoop, Id.run, Id.pure_eq, Id.bind_eq] at h ⊢
  rw [h]
  simp

theorem isPrimeImpLoop_true_iff (n : Nat) :
    isPrimeImpLoop n = true ↔ sixKLoop n 5 (Nat.sqrt n + 1) = true := by
  rw [isPrimeImpLoop_eq, List.all_eq_true, sixKLoop_true_iff]
  constructor
  · intro h j hj hjl
    have hx := h j (List.mem_range.mpr hj)
    exact fun hh => (decide_eq_true_iff.mp hx) ⟨hjl, hh⟩
  · intro h k hk
    rw [decide_eq_true_iff]
    intro hh
    exact (h k (List.mem_range.mp hk) hh.1) hh.2

theorem isPrimeImpLoop_eq_sixKLoop (n : Nat) :
    isPrimeImpLoop n = sixKLoop n 5 (Nat.sqrt n + 1) :=
  Bool_eq_of_true_iff (isPrimeImpLoop_true_iff n)

/-- The imperative implementation computes the same Boolean as the functional one. -/

theorem isPrimeImp_eq (n : Nat) : isPrimeImp n = isPrime n := by
  by_cases h1 : n ≤ 1
  · have a : isPrimeImp n = false := by simp [isPrimeImp, h1]
    have b : isPrime n = false := by simp [isPrime, h1]
    rw [a, b]
  · by_cases h2 : n ≤ 3
    · have a : isPrimeImp n = true := by simp [isPrimeImp, h1, h2]
      have b : isPrime n = true := by simp [isPrime, h1, h2]
      rw [a, b]
    · by_cases h3 : n % 2 = 0 ∨ n % 3 = 0
      · have a : isPrimeImp n = false := by simp [isPrimeImp, h1, h2, h3]
        have b : isPrime n = false := by simp [isPrime, h1, h2, h3]
        rw [a, b]
      · have a : isPrimeImp n = isPrimeImpLoop n := by simp [isPrimeImp, h1, h2, h3]
        have b : isPrime n = sixKLoop n 5 (Nat.sqrt n + 1) := by simp [isPrime, h1, h2, h3]
        rw [a, b, isPrimeImpLoop_eq_sixKLoop]

/-- The imperative `Int` interface is equivalent to the functional one, on the whole domain
(admissible inputs and precondition violations alike). -/

theorem isPrimeIntImp_eq (n : Int) : isPrimeIntImp n = isPrimeInt n := by
  by_cases h : n < 0
  · simp [isPrimeIntImp, isPrimeInt, errMsg, h]
  · simp [isPrimeIntImp, isPrimeInt, h, isPrimeImp_eq]

/-- The imperative implementation satisfies the same specification. -/

theorem isPrimeImp_iff_prime (n : Nat) : isPrimeImp n = true ↔ Nat.Prime n := by
  rw [isPrimeImp_eq, isPrime_iff_prime]

/-- The imperative program is correct with respect to `Pre` and `Post_prop`. -/

theorem correctness_imp_thm (n : Int) (h : Pre n) : Post_prop n (isPrimeIntImp n) := by
  rw [isPrimeIntImp_eq]
  exact correctness_thm n h

/-- The imperative candidate also passes the Python `check` function
(its property-based test is the `native_decide` example in section 11). -/

theorem check_imp_thm : check (fun n => isPrimeIntImp n) = true := by
  have h : (fun n => isPrimeIntImp n) = isPrimeIntImp := rfl
  rw [h]
  have h2 : check isPrimeIntImp = check isPrimeInt := by
    congr 1
    funext n
    exact isPrimeIntImp_eq n
  rw [h2]
  exact check_thm

end «23_is_prime»
