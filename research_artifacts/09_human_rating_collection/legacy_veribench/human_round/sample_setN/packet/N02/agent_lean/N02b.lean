import Mathlib

/-!
# Primality by 6k ± 1 trial division

Translation of the Python `is_prime` routine. Inputs are integers; `Except.error`
models its ValueError, including the original message. The square-root bound is
`Nat.sqrt`: this is the exact discrete interpretation of the mathematical trial
bound, rather than a model of the host Python library's floating-point rounding
or overflow. No floating-point arithmetic is needed for this integer problem.
The range indices represent 5, 11, 17, ... up to that bound; each iteration also
checks the integer two places later, just as in the source.
-/

namespace IsPrime23

deriving instance DecidableEq for Except

def valueError : String := "Input must be non-negative integer"

/-- Number of iterations in `range(5, sqrt(n) + 1, 6)`. -/
def trialCount (n : Nat) : Nat := (Nat.sqrt n + 1) / 6

def trialOK (n k : Nat) : Bool :=
  n % (6 * k + 5) != 0 && n % (6 * k + 7) != 0

def primeNat (n : Nat) : Bool :=
  if n ≤ 1 then false
  else if n ≤ 3 then true
  else if n % 2 == 0 || n % 3 == 0 then false
  else (List.range (trialCount n)).all (trialOK n)

def is_prime (n : Int) : Except String Bool :=
  if n < 0 then .error valueError else .ok (primeNat n.toNat)

/-- Executable translation of the source's public test harness. -/
def check (candidate : Int → Except String Bool) : Bool :=
  decide (candidate 7 = .ok true) && decide (candidate 0 = .ok false) &&
    (match candidate (-1) with
    | .error _ => true
    | .ok _ => false)

example : check is_prime = true := by native_decide
#eval check is_prime

example : is_prime 7 = .ok true := by native_decide
example : is_prime 2 = .ok true := by native_decide
example : is_prime 3 = .ok true := by native_decide
example : is_prime 4 = .ok false := by native_decide
example : is_prime 0 = .ok false := by native_decide
example : is_prime 1 = .ok false := by native_decide
example : is_prime (-1) = .error valueError := by native_decide
example : is_prime 25 = .ok false := by native_decide
example : is_prime 49 = .ok false := by native_decide
example : is_prime 121 = .ok false := by native_decide
example : is_prime 97 = .ok true := by native_decide
#eval is_prime 7
#eval is_prime 0
#eval is_prime (-1)

/-- The `Int` input type enforces the integer-type check; validity adds nonnegativity. -/
def Pre (n : Int) : Prop := 0 ≤ n

lemma trialCount_spec (n k : Nat) :
    k < trialCount n ↔ 6 * k + 5 ≤ Nat.sqrt n := by
  unfold trialCount
  omega

lemma trialOK_spec (n k : Nat) :
    trialOK n k = true ↔ ¬ (6 * k + 5) ∣ n ∧ ¬ (6 * k + 7) ∣ n := by
  simp [trialOK, Nat.dvd_iff_mod_eq_zero]

lemma loop_correct (n : Nat) (hn : 3 < n)
    (h2 : n % 2 ≠ 0) (h3 : n % 3 ≠ 0) :
    (List.range (trialCount n)).all (trialOK n) = true ↔ Nat.Prime n := by
  constructor
  · intro h
    apply Nat.prime_def_le_sqrt.mpr
    refine ⟨by omega, ?_⟩
    intro m hm hs hdiv
    have hm2 : m % 2 ≠ 0 := by
      intro he
      exact h2 (Nat.mod_eq_zero_of_dvd
        (dvd_trans (Nat.dvd_of_mod_eq_zero he) hdiv))
    have hm3 : m % 3 ≠ 0 := by
      intro he
      exact h3 (Nat.mod_eq_zero_of_dvd
        (dvd_trans (Nat.dvd_of_mod_eq_zero he) hdiv))
    have hres : m % 6 = 1 ∨ m % 6 = 5 := by omega
    rcases hres with hr | hr
    · have heq : 6 * (m / 6 - 1) + 7 = m := by omega
      have hk : m / 6 - 1 ∈ List.range (trialCount n) := by
        apply List.mem_range.mpr
        apply (trialCount_spec n _).mpr
        omega
      have ht := (trialOK_spec n _).mp (List.all_eq_true.mp h _ hk)
      exact ht.2 (by simpa only [heq] using hdiv)
    · have heq : 6 * (m / 6) + 5 = m := by omega
      have hk : m / 6 ∈ List.range (trialCount n) := by
        apply List.mem_range.mpr
        apply (trialCount_spec n _).mpr
        omega
      have ht := (trialOK_spec n _).mp (List.all_eq_true.mp h _ hk)
      exact ht.1 (by simpa only [heq] using hdiv)
  · intro hp
    apply List.all_eq_true.mpr
    intro k hk
    apply (trialOK_spec n k).mpr
    have hs : 6 * k + 5 ≤ Nat.sqrt n :=
      (trialCount_spec n k).mp (List.mem_range.mp hk)
    have hsquare : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.le_sqrt.mp (le_refl _)
    have hlt : 6 * k + 7 < n := by nlinarith
    exact ⟨(Nat.prime_def_lt'.mp hp).2 _ (by omega) (by omega),
      (Nat.prime_def_lt'.mp hp).2 _ (by omega) hlt⟩

theorem primeNat_correct (n : Nat) : primeNat n = true ↔ Nat.Prime n := by
  by_cases h1 : n ≤ 1
  · have hp : ¬Nat.Prime n := by
      intro hp
      have := hp.two_le
      omega
    simp [primeNat, h1, hp]
  by_cases hs : n ≤ 3
  · have hp : Nat.Prime n := by
      have : n = 2 ∨ n = 3 := by omega
      rcases this with rfl | rfl <;> norm_num
    simp [primeNat, h1, hs, hp]
  by_cases h2 : n % 2 = 0
  · have hp : ¬Nat.Prime n := by
      intro hp
      have := hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero h2)
      omega
    simp [primeNat, h1, hs, h2, hp]
  by_cases h3 : n % 3 = 0
  · have hp : ¬Nat.Prime n := by
      intro hp
      have := hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h3)
      omega
    simp [primeNat, h1, hs, h3, hp]
  simpa [primeNat, h1, hs, h2, h3] using loop_correct n (by omega) h2 h3



/-- The Boolean result is exactly mathematical primality. -/
def primality_prop (n : Int) : Prop :=
  is_prime n = .ok (decide (Nat.Prime n.toNat))

theorem primality_thm (n : Int) (hn : Pre n) : primality_prop n := by
  have hnonneg : ¬n < 0 := by unfold Pre at hn; omega
  unfold primality_prop is_prime
  rw [if_neg hnonneg]
  congr 1
  have h := primeNat_correct n.toNat
  cases he : primeNat n.toNat <;> simp_all

/-- The usual definition: at least two, with no divisors except one and itself. -/
def divisor_characterization_prop (n : Int) : Prop :=
  is_prime n = .ok true ↔
    2 ≤ n ∧ ∀ d : Nat, d ∣ n.toNat → d = 1 ∨ d = n.toNat

theorem divisor_characterization_thm (n : Int) (hn : Pre n) :
    divisor_characterization_prop n := by
  have hr := primality_thm n hn
  unfold primality_prop at hr
  unfold divisor_characterization_prop
  rw [hr]
  have hcast : (2 ≤ n.toNat ↔ 2 ≤ n) := by unfold Pre at hn; omega
  simp only [Except.ok.injEq, decide_eq_true_eq, Nat.prime_def]
  rw [hcast]

/-- Both initial small-number branches, on admissible inputs. -/
def edge_prop (n : Int) : Prop :=
  (n ≤ 1 → is_prime n = .ok false) ∧
  (2 ≤ n ∧ n ≤ 3 → is_prime n = .ok true)

theorem edge_thm (n : Int) (hn : Pre n) : edge_prop n := by
  have hnonneg : ¬n < 0 := by unfold Pre at hn; omega
  constructor
  · intro hs
    have ht : n.toNat ≤ 1 := by omega
    simp [is_prime, hnonneg, primeNat, ht]
  · intro hs
    have ht1 : ¬n.toNat ≤ 1 := by omega
    have ht3 : n.toNat ≤ 3 := by omega
    simp [is_prime, hnonneg, primeNat, ht1, ht3]

/-- Above three, multiples of either two or three are immediately rejected. -/
def small_divisor_prop (n : Int) : Prop :=
  3 < n → (n.toNat % 2 = 0 ∨ n.toNat % 3 = 0) → is_prime n = .ok false

theorem small_divisor_thm (n : Int) : small_divisor_prop n := by
  intro hlarge hdiv
  have hnonneg : ¬n < 0 := by omega
  have h1 : ¬n.toNat ≤ 1 := by omega
  have h3 : ¬n.toNat ≤ 3 := by omega
  rcases hdiv with h | h <;> simp [is_prime, hnonneg, primeNat, h1, h3, h]

/-- Precisely the inadmissible inputs raise the modelled ValueError. -/
def error_prop (n : Int) : Prop :=
  is_prime n = .error valueError ↔ ¬Pre n

theorem error_thm (n : Int) : error_prop n := by
  by_cases h : n < 0
  · simp [error_prop, is_prime, Pre, h, show ¬0 ≤ n by omega]
  · simp [error_prop, is_prime, Pre, h, show 0 ≤ n by omega]

/-- All behavioral guarantees for a valid call, including the absence of an error. -/
def Post_prop (n : Int) : Prop :=
  primality_prop n ∧ divisor_characterization_prop n ∧ edge_prop n ∧
    small_divisor_prop n ∧ error_prop n

/-! ## Property-based tests

Each check below is an executable form of the named property. For the unbounded
quantification in `divisor_characterization_prop`, divisors of a positive natural
are bounded by that natural. Thus enumeration through `n` is its finite test
counterpart; the separate `2 ≤ n` check also deals with zero and one.
These exhaustive small-domain checks are evidence, not proofs of the theorems.
-/

def primalityCheck (n : Int) : Bool :=
  decide (is_prime n = .ok (decide (Nat.Prime n.toNat)))

def divisorCheck (n : Int) : Bool :=
  decide (is_prime n = .ok true) ==
    (decide (2 ≤ n) && (List.range (n.toNat + 1)).all
      (fun d => decide (d ∣ n.toNat → d = 1 ∨ d = n.toNat)))

def edgeCheck (n : Int) : Bool :=
  decide ((n ≤ 1 → is_prime n = .ok false) ∧
    (2 ≤ n ∧ n ≤ 3 → is_prime n = .ok true))

def smallDivisorCheck (n : Int) : Bool :=
  decide (3 < n → (n.toNat % 2 = 0 ∨ n.toNat % 3 = 0) →
    is_prime n = .ok false)

def errorCheck (n : Int) : Bool :=
  decide ((is_prime n = .error valueError) ↔ ¬0 ≤ n)

def postCheck (n : Int) : Bool :=
  primalityCheck n && divisorCheck n && edgeCheck n &&
    smallDivisorCheck n && errorCheck n

-- PBT for primality_prop.
example : (List.range 500).all (fun n => primalityCheck (n : Int)) = true := by
  native_decide
-- PBT for divisor_characterization_prop.
example : (List.range 500).all (fun n => divisorCheck (n : Int)) = true := by
  native_decide
-- PBT for edge_prop, with valid inputs as required by its theorem.
example : (List.range 500).all (fun n => edgeCheck (n : Int)) = true := by
  native_decide
-- PBT for small_divisor_prop, including invalid inputs (where its premise is false).
example : (List.range 1000).all
    (fun n => smallDivisorCheck ((n : Int) - 500)) = true := by native_decide
-- PBT for error_prop: both valid and invalid inputs are sampled exhaustively.
example : (List.range 1000).all
    (fun n => errorCheck ((n : Int) - 500)) = true := by native_decide
-- PBT for the full post-condition on admissible inputs.
example : (List.range 500).all (fun n => postCheck (n : Int)) = true := by
  native_decide
#eval (List.range 500).all (fun n => postCheck (n : Int))

/-- Correctness for every input satisfying the source precondition. -/
theorem correctness (n : Int) : Pre n → Post_prop n := by
  intro hn
  exact ⟨primality_thm n hn, divisor_characterization_thm n hn,
    edge_thm n hn, small_divisor_thm n, error_thm n⟩

/-- Mutable-state translation of the trial loop and the early branches.
A false flag remains false: later iterations do not change the returned value,
so this also models the source's early return from a failed trial. -/
def primeNatImp (n : Nat) : Bool := Id.run do
  if n ≤ 1 then return false
  if n ≤ 3 then return true
  if n % 2 == 0 || n % 3 == 0 then return false
  let mut ok := true
  for k in List.range (trialCount n) do
    if n % (6 * k + 5) == 0 || n % (6 * k + 7) == 0 then
      ok := false
  return ok

def is_prime_imp (n : Int) : Except String Bool := Id.run do
  if n < 0 then return .error valueError
  let answer := primeNatImp n.toNat
  return .ok answer

example : is_prime_imp 7 = .ok true := by native_decide
example : is_prime_imp 0 = .ok false := by native_decide
example : is_prime_imp (-1) = .error valueError := by native_decide
example : is_prime_imp 49 = .ok false := by native_decide
#eval is_prime_imp 97

example : check is_prime_imp = true := by native_decide
example : (List.range 1000).all (fun n =>
    decide (is_prime ((n : Int) - 500) = is_prime_imp ((n : Int) - 500))) = true := by
  native_decide
#eval check is_prime_imp

/-- Loop invariant, valid for either initial flag and any remaining index list. -/
lemma mutable_loop_eq (n : Nat) (ks : List Nat) (b : Bool) :
    (Id.run do
      let mut ok := b
      for k in ks do
        if n % (6 * k + 5) == 0 || n % (6 * k + 7) == 0 then
          ok := false
      return ok) = (b && ks.all (trialOK n)) := by
  induction ks generalizing b with
  | nil => simp
  | cons k ks ih =>
    simp only [List.forIn_cons, List.all_cons]
    split <;> cases b <;> simp_all [trialOK]
    all_goals aesop

/-- Equivalence of the natural-number cores, proved by the loop invariant. -/
theorem primeNat_equivalence (n : Nat) : primeNat n = primeNatImp n := by
  by_cases h1 : n ≤ 1
  · simp [primeNat, primeNatImp, h1]
  by_cases h3 : n ≤ 3
  · simp [primeNat, primeNatImp, h1, h3]
  by_cases hd : (n % 2 == 0 || n % 3 == 0) = true
  · simp [primeNat, primeNatImp, h1, h3, hd]
  · simpa [primeNat, primeNatImp, h1, h3, hd] using
      (mutable_loop_eq n (List.range (trialCount n)) true).symm

/-- All-input equivalence, including the invalid-input exception branch. -/
theorem functional_imperative_equivalence (n : Int) :
    is_prime n = is_prime_imp n := by
  by_cases h : n < 0 <;> simp [is_prime, is_prime_imp, h, primeNat_equivalence]

end IsPrime23
