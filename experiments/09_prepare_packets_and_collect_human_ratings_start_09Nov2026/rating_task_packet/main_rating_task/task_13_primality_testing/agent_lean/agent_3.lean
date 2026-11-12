import Mathlib
import Plausible

/-!
# VeriBench 23: `is_prime`

Lean 4 translation of the Python primality checker.

The Python function accepts an integer and raises `ValueError` unless the input is
a non-negative integer. On a valid input it returns whether that integer is prime,
using trial division by `2`, by `3`, and by integers of the form `6k ± 1` up to
`floor(sqrt(n))`.

`math.sqrt` is used in Python only to compute that integer loop bound. The
mathematical intent is the floor square root, modelled here by `Nat.sqrt`
(`int(math.sqrt(n))` for the exact floor, which is what the algorithm requires).
The result itself is Boolean, so the specification is stated over `Nat` / `Int`,
not IEEE-754 `Float`.
-/

namespace «23_is_prime»

/-- Error string matching Python `ValueError("Input must be non-negative integer")`. -/
def errorMsg : String := "Input must be non-negative integer"

instance : DecidableEq (Except String Bool) := fun a b =>
  match a, b with
  | Except.error s1, Except.error s2 =>
      if h : s1 = s2 then isTrue (by cases h; rfl) else isFalse (by intro hEq; cases hEq; exact h rfl)
  | Except.ok b1, Except.ok b2 =>
      if h : b1 = b2 then isTrue (by cases h; rfl) else isFalse (by intro hEq; cases hEq; exact h rfl)
  | Except.error _, Except.ok _ => isFalse (by intro h; cases h)
  | Except.ok _, Except.error _ => isFalse (by intro h; cases h)

def trialAcc (n : Nat) (ok : Bool) (i : Nat) : Bool :=
  if 5 ≤ i ∧ (i - 5) % 6 = 0 then
    ok && (n % i != 0 && n % (i + 2) != 0)
  else
    ok

def trialFold (n bound : Nat) : Bool :=
  (List.range bound).foldl (trialAcc n) true

def isPrime (n : Nat) : Bool :=
  if n ≤ 1 then false
  else if n ≤ 3 then true
  else if n % 2 == 0 || n % 3 == 0 then false
  else trialFold n (n.sqrt + 1)

lemma trialFold_succ (n bound : Nat) :
    trialFold n (bound + 1) = trialAcc n (trialFold n bound) bound := by
  unfold trialFold
  simp [List.range_succ, List.foldl_append]

lemma trialFold_true_iff (n bound : Nat) :
    trialFold n bound = true ↔
      ∀ i, i < bound → 5 ≤ i → (i - 5) % 6 = 0 →
        n % i ≠ 0 ∧ n % (i + 2) ≠ 0 := by
  induction bound with
  | zero =>
    unfold trialFold
    simp
  | succ bound ih =>
    rw [trialFold_succ]
    by_cases h : 5 ≤ bound ∧ (bound - 5) % 6 = 0
    · unfold trialAcc
      rw [if_pos h]
      constructor
      · intro htrue i hi h5 h6
        have hconj : trialFold n bound = true ∧ n % bound ≠ 0 ∧ n % (bound + 2) ≠ 0 := by
          simpa using htrue
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · exact (ih.mp hconj.1) i hlt h5 h6
        · exact ⟨hconj.2.1, hconj.2.2⟩
      · intro hall
        have hfold : trialFold n bound = true :=
          ih.mpr (fun i hi h5 h6 => hall i (Nat.lt_succ_of_lt hi) h5 h6)
        have hmods := hall bound (Nat.lt_succ_self _) h.1 h.2
        simp [hfold, hmods]
    · unfold trialAcc
      rw [if_neg h]
      constructor
      · intro hfold i hi h5 h6
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · exact (ih.mp hfold) i hlt h5 h6
        · exact (h ⟨h5, h6⟩).elim
      · intro hall
        exact ih.mpr (fun i hi h5 h6 => hall i (Nat.lt_succ_of_lt hi) h5 h6)

lemma mod6_one_or_five {m : Nat} (h2 : ¬ 2 ∣ m) (h3 : ¬ 3 ∣ m) :
    m % 6 = 1 ∨ m % 6 = 5 := by
  have hlt : m % 6 < 6 := Nat.mod_lt _ (by decide)
  generalize hr : m % 6 = r at hlt
  interval_cases r
  · have : 2 ∣ m := by
      have := Nat.mod_add_div m 6
      omega
    exact (h2 this).elim
  · left; omega
  · have : 2 ∣ m := by
      have := Nat.mod_add_div m 6
      omega
    exact (h2 this).elim
  · have : 3 ∣ m := by
      have := Nat.mod_add_div m 6
      omega
    exact (h3 this).elim
  · have : 2 ∣ m := by
      have := Nat.mod_add_div m 6
      omega
    exact (h2 this).elim
  · right; omega

lemma sqrt_lt_sub_two {n : Nat} (hn : 5 ≤ n) : n.sqrt < n - 2 := by
  apply (Nat.sqrt_lt).2
  have h1 : 3 * (n - 2) ≤ (n - 2) * (n - 2) := by
    apply Nat.mul_le_mul_right
    omega
  have h2 : n < 3 * (n - 2) := by
    have : 3 * (n - 2) = 3 * n - 6 := by omega
    omega
  omega

lemma sub_mod_of_mod_one {m : Nat} (h : m % 6 = 1) (hm : 7 ≤ m) :
    (m - 2 - 5) % 6 = 0 := by
  have := Nat.mod_add_div m 6
  have : m - 7 = 6 * (m / 6 - 1) := by omega
  have : 6 ∣ (m - 2 - 5) := by
    use m / 6 - 1
    omega
  exact Nat.mod_eq_zero_of_dvd this

lemma sub_mod_of_mod_five {m : Nat} (h : m % 6 = 5) (_hm : 5 ≤ m) :
    (m - 5) % 6 = 0 := by
  have := Nat.mod_add_div m 6
  have : 6 ∣ (m - 5) := by
    use m / 6
    omega
  exact Nat.mod_eq_zero_of_dvd this

lemma not_dvd_of_trial {n : Nat} (h2 : n % 2 ≠ 0) (h3 : n % 3 ≠ 0)
    (htrial : trialFold n (n.sqrt + 1) = true)
    {m : Nat} (hm2 : 2 ≤ m) (hmle : m ≤ n.sqrt) : ¬ m ∣ n := by
  intro hdvd
  have h2n : ¬ 2 ∣ n := by simpa [Nat.dvd_iff_mod_eq_zero] using h2
  have h3n : ¬ 3 ∣ n := by simpa [Nat.dvd_iff_mod_eq_zero] using h3
  have h2m : ¬ 2 ∣ m := fun h => h2n (dvd_trans h hdvd)
  have h3m : ¬ 3 ∣ m := fun h => h3n (dvd_trans h hdvd)
  have hmod := mod6_one_or_five h2m h3m
  have hforall := (trialFold_true_iff n (n.sqrt + 1)).mp htrial
  rcases hmod with h1 | h5
  · have hmge : 7 ≤ m := by
      have := Nat.mod_add_div m 6
      omega
    have hi5 : 5 ≤ m - 2 := by omega
    have hi6 : (m - 2 - 5) % 6 = 0 := sub_mod_of_mod_one h1 hmge
    have hilt : m - 2 < n.sqrt + 1 := by omega
    have hbad := hforall (m - 2) hilt hi5 hi6
    have : n % m ≠ 0 := by
      have hi2 : m - 2 + 2 = m := by omega
      simpa [hi2] using hbad.2
    exact this (Nat.mod_eq_zero_of_dvd hdvd)
  · have hmge : 5 ≤ m := by
      have := Nat.mod_add_div m 6
      omega
    have h6 : (m - 5) % 6 = 0 := sub_mod_of_mod_five h5 hmge
    have hlt : m < n.sqrt + 1 := by omega
    have hbad := hforall m hlt hmge h6
    exact hbad.1 (Nat.mod_eq_zero_of_dvd hdvd)
/-- Full Python entry point: reject negative inputs, otherwise test primality. -/
def is_prime (n : Int) : Except String Bool :=
  if n < 0 then
    Except.error errorMsg
  else
    Except.ok (isPrime n.toNat)

/-! ## Unit tests -/

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
example : is_prime (-1) = Except.error errorMsg := by native_decide
example : is_prime 7 = Except.ok true := by native_decide
example : is_prime 0 = Except.ok false := by native_decide
example : is_prime 4 = Except.ok false := by native_decide

#eval isPrime 7
#eval isPrime 4
#eval isPrime 0
#eval is_prime (-1)
#eval (List.range 40).filter isPrime

/-! ## Pre-condition -/

/-- Python `pre`: input is an integer (enforced by `Int`) and non-negative. -/
def Pre (n : Int) : Prop := 0 ≤ n

/-- Boolean form of `Pre`, matching Python `pre`. -/
def pre (n : Int) : Bool := decide (0 ≤ n)

def pre_iff_Pre_prop (n : Int) : Prop := pre n = true ↔ Pre n

theorem pre_iff_Pre_thm (n : Int) : pre_iff_Pre_prop n := by
  simp [pre_iff_Pre_prop, pre, Pre]

/-! ## Property propositions and theorems -/

def isPrime_iff_prime_prop (n : Nat) : Prop :=
  isPrime n = true ↔ n.Prime

theorem isPrime_iff_prime_thm (n : Nat) : isPrime n = true ↔ n.Prime := by
  constructor
  · intro h
    by_cases h1 : n ≤ 1
    · unfold isPrime at h
      simp [h1] at h
    · by_cases h3 : n ≤ 3
      · have : n = 2 ∨ n = 3 := by omega
        rcases this with rfl | rfl
        · exact Nat.prime_two
        · exact Nat.prime_three
      · unfold isPrime at h
        simp only [h1, h3, ite_false] at h
        by_cases hdiv : (n % 2 == 0 || n % 3 == 0) = true
        · simp [hdiv] at h
        · have htrial : trialFold n (n.sqrt + 1) = true := by simpa [hdiv] using h
          have h2 : n % 2 ≠ 0 := by
            intro he
            apply hdiv
            simp [he]
          have h3m : n % 3 ≠ 0 := by
            intro he
            apply hdiv
            simp [he]
          have hn2 : 2 ≤ n := by omega
          refine (Nat.prime_def_le_sqrt).2 ⟨hn2, ?_⟩
          intro m hm2 hmle
          exact not_dvd_of_trial h2 h3m htrial hm2 hmle
  · intro hp
    have hn2 : 2 ≤ n := hp.two_le
    by_cases h3 : n ≤ 3
    · have : n = 2 ∨ n = 3 := by omega
      rcases this with rfl | rfl <;> decide
    · unfold isPrime
      have h1 : ¬ n ≤ 1 := by omega
      simp only [h1, h3, ite_false]
      have h2mod : n % 2 ≠ 0 := by
        intro hmod
        have hd : 2 ∣ n := Nat.dvd_of_mod_eq_zero hmod
        have : 2 = n := (Nat.dvd_prime_two_le hp (by decide)).mp hd
        omega
      have h3mod : n % 3 ≠ 0 := by
        intro hmod
        have hd : 3 ∣ n := Nat.dvd_of_mod_eq_zero hmod
        have : 3 = n := (Nat.dvd_prime_two_le hp (by decide)).mp hd
        omega
      have hdiv : (n % 2 == 0 || n % 3 == 0) = false := by
        simp [h2mod, h3mod]
      simp only [hdiv]
      apply (trialFold_true_iff n (n.sqrt + 1)).2
      intro i hi h5 h6
      constructor
      · intro hmod
        have hd : i ∣ n := Nat.dvd_of_mod_eq_zero hmod
        have hi2 : 2 ≤ i := by omega
        have hile : i ≤ n.sqrt := by omega
        exact (Nat.prime_def_le_sqrt.mp hp).2 i hi2 hile hd
      · intro hmod
        have hd : i + 2 ∣ n := Nat.dvd_of_mod_eq_zero hmod
        have hi2 : 2 ≤ i + 2 := by omega
        by_cases hle : i + 2 ≤ n.sqrt
        · exact (Nat.prime_def_le_sqrt.mp hp).2 (i + 2) hi2 hle hd
        · have heq : i + 2 = n := (Nat.dvd_prime_two_le hp hi2).mp hd
          have hlt := sqrt_lt_sub_two (by omega : 5 ≤ n)
          have : i ≤ n.sqrt := by omega
          omega

def prime_doc_prop (n : Nat) : Prop :=
  isPrime n = true ↔ 2 ≤ n ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

theorem prime_doc_thm (n : Nat) : prime_doc_prop n := by
  unfold prime_doc_prop
  rw [isPrime_iff_prime_thm, Nat.prime_def]

def zero_not_prime_prop : Prop := isPrime 0 = false

theorem zero_not_prime_thm : zero_not_prime_prop := by
  unfold zero_not_prime_prop isPrime
  decide

def one_not_prime_prop : Prop := isPrime 1 = false

theorem one_not_prime_thm : one_not_prime_prop := by
  unfold one_not_prime_prop isPrime
  decide

def two_prime_prop : Prop := isPrime 2 = true

theorem two_prime_thm : two_prime_prop :=
  (isPrime_iff_prime_thm 2).2 Nat.prime_two

def three_prime_prop : Prop := isPrime 3 = true

theorem three_prime_thm : three_prime_prop :=
  (isPrime_iff_prime_thm 3).2 Nat.prime_three

def four_not_prime_prop : Prop := isPrime 4 = false

theorem four_not_prime_thm : four_not_prime_prop := by
  have h : ¬ Nat.Prime 4 := by decide
  have hne : isPrime 4 ≠ true := (isPrime_iff_prime_thm 4).not.mpr h
  unfold four_not_prime_prop
  cases h' : isPrime 4 <;> simp_all

def seven_prime_prop : Prop := isPrime 7 = true

theorem seven_prime_thm : seven_prime_prop :=
  (isPrime_iff_prime_thm 7).2 (by decide)

def le_one_not_prime_prop (n : Nat) : Prop :=
  n ≤ 1 → isPrime n = false

theorem le_one_not_prime_thm (n : Nat) : le_one_not_prime_prop n := by
  intro h
  unfold isPrime
  simp [h]

def two_or_three_prime_prop (n : Nat) : Prop :=
  n = 2 ∨ n = 3 → isPrime n = true

theorem two_or_three_prime_thm (n : Nat) : two_or_three_prime_prop n := by
  intro h
  rcases h with rfl | rfl
  · exact two_prime_thm
  · exact three_prime_thm

def even_not_prime_prop (n : Nat) : Prop :=
  2 < n → n % 2 = 0 → isPrime n = false

theorem even_not_prime_thm (n : Nat) : even_not_prime_prop n := by
  intro hn he
  unfold isPrime
  have h1 : ¬ n ≤ 1 := by omega
  have h3 : ¬ n ≤ 3 := by omega
  simp only [h1, h3, ite_false]
  simp [he]

def multiple_of_three_not_prime_prop (n : Nat) : Prop :=
  3 < n → n % 3 = 0 → isPrime n = false

theorem multiple_of_three_not_prime_thm (n : Nat) : multiple_of_three_not_prime_prop n := by
  intro hn he
  unfold isPrime
  have h1 : ¬ n ≤ 1 := by omega
  have h3 : ¬ n ≤ 3 := by omega
  simp only [h1, h3, ite_false]
  have hor : (n % 2 == 0 || n % 3 == 0) = true := by simp [he]
  simp [hor]

/-- On the main branch the implementation is exactly the Python `6k ± 1` loop. -/
def trial_division_prop (n : Nat) : Prop :=
  3 < n → n % 2 ≠ 0 → n % 3 ≠ 0 →
    (isPrime n = true ↔
      ∀ i, i ≤ n.sqrt → 5 ≤ i → (i - 5) % 6 = 0 →
        n % i ≠ 0 ∧ n % (i + 2) ≠ 0)

theorem trial_division_thm (n : Nat) : trial_division_prop n := by
  intro hn h2 h3
  unfold isPrime
  have h1 : ¬ n ≤ 1 := by omega
  have hle : ¬ n ≤ 3 := by omega
  simp only [h1, hle, ite_false]
  have hdiv : (n % 2 == 0 || n % 3 == 0) = false := by
    simp [h2, h3]
  rw [hdiv]
  simp [trialFold_true_iff, Nat.lt_succ_iff]

def neg_raises_prop (n : Int) : Prop :=
  n < 0 → is_prime n = Except.error errorMsg

theorem neg_raises_thm (n : Int) : neg_raises_prop n := by
  intro h
  unfold is_prime
  simp [h]

def nonneg_agrees_prop (n : Int) : Prop :=
  0 ≤ n → is_prime n = Except.ok (isPrime n.toNat)

theorem nonneg_agrees_thm (n : Int) : nonneg_agrees_prop n := by
  intro h
  unfold is_prime
  rw [if_neg (not_lt_of_ge h)]

def result_iff_prime_prop (n : Int) : Prop :=
  0 ≤ n → (is_prime n = Except.ok true ↔ (n.toNat).Prime)

theorem result_iff_prime_thm (n : Int) : result_iff_prime_prop n := by
  intro h
  rw [nonneg_agrees_thm n h]
  simpa using isPrime_iff_prime_thm n.toNat

/-- Python `check`: basic case, edge case, and negative pre-violation. -/
def check (candidate : Int → Except String Bool) : Bool :=
  (candidate 7 == Except.ok true) &&
  (candidate 0 == Except.ok false) &&
  (match candidate (-1) with
   | Except.error _ => true
   | Except.ok _ => false)

theorem check_is_prime_thm : check is_prime = true := by
  unfold check
  decide

/-! ## Post-condition -/

/-- Successful run agrees with the mathematical definition of primality,
the implementation, the documented edge cases, and the early exits. -/
def Post_prop (n : Int) : Prop :=
  result_iff_prime_prop n ∧
  prime_doc_prop n.toNat ∧
  nonneg_agrees_prop n ∧
  le_one_not_prime_prop n.toNat ∧
  two_or_three_prime_prop n.toNat ∧
  even_not_prime_prop n.toNat ∧
  multiple_of_three_not_prime_prop n.toNat ∧
  (0 ≤ n → (is_prime n = Except.ok true ↔
    2 ≤ n.toNat ∧ ∀ m, m ∣ n.toNat → m = 1 ∨ m = n.toNat))

/-! ## Property-based tests -/

/-- Executable Boolean form of `Post_prop` on a non-negative input.
The `Real` square-root bound is not part of the result; the executable
counterpart of the loop bound is `Nat.sqrt`. -/
def postBool (n : Nat) : Bool :=
  (isPrime n == decide (n.Prime)) &&
  (match is_prime (n : Int) with
    | Except.ok b => b == isPrime n
    | Except.error _ => false) &&
  (!(decide (n ≤ 1)) || isPrime n == false) &&
  (!(decide (n = 2 ∨ n = 3)) || isPrime n == true) &&
  (!(decide (2 < n)) || !(n % 2 == 0) || isPrime n == false) &&
  (!(decide (3 < n)) || !(n % 3 == 0) || isPrime n == false)

def noProperDivisor (n : Nat) : Bool :=
  (List.range n).all (fun m => !(decide (2 ≤ m)) || !(decide (m ∣ n)) || m == n)

example : (List.range 50).all postBool = true := by native_decide
example : (List.range 50).all (fun n => isPrime n == decide (n.Prime)) = true := by native_decide
example : (List.range 40).all (fun n => isPrime n == (decide (2 ≤ n) && noProperDivisor n)) = true := by native_decide
example : (List.range 40).all (fun n => !(decide (2 < n)) || !(n % 2 == 0) || isPrime n == false) = true := by native_decide
example : (List.range 40).all (fun n => !(decide (3 < n)) || !(n % 3 == 0) || isPrime n == false) = true := by native_decide
example : (List.range 30).all (fun i =>
    match is_prime (-(Int.ofNat (i + 1))) with
    | Except.error _ => true
    | Except.ok _ => false) = true := by native_decide
example : (List.range 40).all (fun n =>
    match is_prime (n : Int) with
    | Except.ok b => b == isPrime n
    | Except.error _ => false) = true := by native_decide
example : (List.range 40).all (fun n =>
    !(decide (3 < n)) || !(decide (n % 2 ≠ 0)) || !(decide (n % 3 ≠ 0)) ||
      (isPrime n ==
        ((List.range (n.sqrt + 1)).all (fun i =>
          !(decide (5 ≤ i ∧ (i - 5) % 6 = 0)) ||
            (n % i != 0 && n % (i + 2) != 0))))) = true := by native_decide
example : (List.range 20).all (fun n => pre (n : Int) == true) = true := by native_decide
example : (List.range 20).all (fun i => pre (-(Int.ofNat (i + 1))) == false) = true := by native_decide

#eval isPrime 0 == false
#eval isPrime 1 == false
#eval isPrime 2 == true
#eval isPrime 3 == true
#eval isPrime 4 == false
#eval isPrime 7 == true
#eval pre (-1) == false
#eval pre 5 == true

#eval Plausible.Testable.check (∀ n : Nat, isPrime n = decide (n.Prime))
#eval Plausible.Testable.check (∀ n : Nat, !(decide (2 < n)) || !(n % 2 == 0) || isPrime n = false)
#eval Plausible.Testable.check (∀ n : Nat, !(decide (3 < n)) || !(n % 3 == 0) || isPrime n = false)
#eval Plausible.Testable.check (∀ n : Int, !(decide (n < 0)) || is_prime n = Except.error errorMsg)
#eval Plausible.Testable.check (∀ n : Nat, is_prime (n : Int) = Except.ok (isPrime n))
#eval Plausible.Testable.check (∀ n : Nat, is_prime (n : Int) = Except.ok true ↔ n.Prime)
#eval Plausible.Testable.check (∀ n : Int, pre n = decide (0 ≤ n))

/-! ## Correctness -/

theorem correctness_thm (n : Int) (hpre : Pre n) : Post_prop n := by
  unfold Post_prop
  refine ⟨result_iff_prime_thm n, prime_doc_thm _, nonneg_agrees_thm n,
    le_one_not_prime_thm _, two_or_three_prime_thm _, even_not_prime_thm _,
    multiple_of_three_not_prime_thm _, ?_⟩
  intro _
  rw [nonneg_agrees_thm n hpre]
  simpa [Nat.prime_def] using isPrime_iff_prime_thm n.toNat

/-! ## Imperative implementation -/

/-- Imperative trial division with mutable state, matching the Python loop. -/
def isPrimeImp (n : Nat) : Bool :=
  Id.run do
    if n ≤ 1 then
      return false
    if n ≤ 3 then
      return true
    if n % 2 == 0 || n % 3 == 0 then
      return false
    let mut ok : Bool := true
    for i in List.range (Nat.sqrt n + 1) do
      ok := trialAcc n ok i
    return ok

/-- Imperative wrapper that raises on negative inputs. -/
def is_primeImp (n : Int) : Except String Bool :=
  Id.run do
    if n < 0 then
      return Except.error errorMsg
    return Except.ok (isPrimeImp n.toNat)

/-! ## Imperative tests -/

example : isPrimeImp 2 = true := by native_decide
example : isPrimeImp 4 = false := by native_decide
example : isPrimeImp 0 = false := by native_decide
example : isPrimeImp 1 = false := by native_decide
example : isPrimeImp 7 = true := by native_decide
example : isPrimeImp 9 = false := by native_decide
example : isPrimeImp 25 = false := by native_decide
example : isPrimeImp 97 = true := by native_decide
example : is_primeImp (-1) = Except.error errorMsg := by native_decide
example : is_primeImp 7 = Except.ok true := by native_decide
example : is_primeImp 0 = Except.ok false := by native_decide

#eval isPrimeImp 7
#eval isPrimeImp 25
#eval is_primeImp (-5)
#eval (List.range 40).filter isPrimeImp

/-! ## Equivalence -/

theorem isPrime_eq_isPrimeImp_thm (n : Nat) : isPrime n = isPrimeImp n := by
  unfold isPrime isPrimeImp trialFold
  simp only [Id.run]
  split_ifs <;> try rfl
  simp only [bind_pure_comp, pure_bind, map_pure, bind_pure]
  apply Eq.symm
  rw [List.forIn_pure_yield_eq_foldl]
  rfl

theorem is_prime_eq_is_primeImp_thm (n : Int) : is_prime n = is_primeImp n := by
  unfold is_prime is_primeImp
  simp only [Id.run, isPrime_eq_isPrimeImp_thm]
  split_ifs <;> rfl

theorem check_is_primeImp_thm : check is_primeImp = true := by
  have hfun := check_is_prime_thm
  unfold check at hfun ⊢
  simp [is_prime_eq_is_primeImp_thm] at hfun ⊢
  exact hfun

end «23_is_prime»
