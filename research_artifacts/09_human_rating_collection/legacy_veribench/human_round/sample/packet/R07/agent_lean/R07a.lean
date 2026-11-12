import Mathlib

/-!
# `is_prime` — primality test for non-negative integers

Lean 4 formalization of the Python program `23_is_prime.py`.

The Python function

* raises `ValueError` when the input is negative (the precondition `pre(n) := n ≥ 0`
  fails),
* returns `False` for `n ≤ 1`,
* returns `True` for `n = 2, 3`,
* returns `False` when `2 ∣ n` or `3 ∣ n`,
* and otherwise runs the `6k ± 1` wheel `for i in range(5, int(sqrt(n)) + 1, 6)`,
  testing divisibility by `i` and by `i + 2`.

We model the integer square root `int(math.sqrt(n))` by `Nat.sqrt n`.

The file provides a functional model (`isPrime`), a total model that also records the
`ValueError` branch (`isPrimeE`), the specification (`Pre` / `Post_prop`), a proof that
the wheel algorithm really decides primality, an imperative `Id.run do` implementation
and a proof that the two implementations agree.
-/

namespace «23_is_prime»

/-! ## Implementation (functional) -/

/-- Number of iterations performed by `range(5, int(sqrt n) + 1, 6)`. -/
def numSteps (n : Nat) : Nat :=
  if Nat.sqrt n < 5 then 0 else (Nat.sqrt n - 5) / 6 + 1

/-- The list of loop values `i` visited by `range(5, int(sqrt n) + 1, 6)`,
i.e. `[5, 11, 17, …]` up to `Nat.sqrt n`. -/
def wheelCandidates (n : Nat) : List Nat :=
  List.range' 5 (numSteps n) 6

/-- The primality test, on `Nat` (the domain where the Python precondition holds). -/
def isPrimeNat (n : Nat) : Bool :=
  if n ≤ 1 then false
  else if n ≤ 3 then true
  else if n % 2 == 0 || n % 3 == 0 then false
  else (wheelCandidates n).all (fun i => !(n % i == 0) && !(n % (i + 2) == 0))

/-- Functional model of `is_prime`, on `Int` inputs satisfying the precondition. -/
def isPrime (n : Int) : Bool :=
  isPrimeNat n.toNat

/-- Total model of `is_prime` including the `ValueError` branch of the Python code. -/
def isPrimeE (n : Int) : Except String Bool :=
  if 0 ≤ n then Except.ok (isPrime n)
  else Except.error "Input must be non-negative integer"

/-! ## Unit tests (mirroring the Python `check`) -/

example : isPrime 7 = true := by native_decide
example : isPrime 0 = false := by native_decide
example : isPrimeE (-1) = Except.error "Input must be non-negative integer" := by
  simp [isPrimeE]

example : isPrime 2 = true := by native_decide
example : isPrime 4 = false := by native_decide
example : isPrime 1 = false := by native_decide
example : isPrime 3 = true := by native_decide
example : isPrime 25 = false := by native_decide
example : isPrime 49 = false := by native_decide
example : isPrime 121 = false := by native_decide
example : isPrime 97 = true := by native_decide
example : isPrime 7919 = true := by native_decide

#eval isPrime 7      -- true
#eval isPrime 0      -- false
#eval isPrimeE (-1)  -- Except.error "Input must be non-negative integer"
#eval (List.range 30).filter (fun n => isPrime (n : Int))

/-- Cross-check against Mathlib's `Nat.Prime` on an initial segment. -/
example : ∀ n ∈ List.range 300, (isPrime (n : Int) = true ↔ Nat.Prime n) := by native_decide

/-! ## Pre-condition -/

/-- Python's `pre(n) : bool` : the input must be a non-negative integer. -/
def Pre (n : Int) : Prop := 0 ≤ n

instance (n : Int) : Decidable (Pre n) := by unfold Pre; infer_instance

/-! ## Auxiliary lemmas about the wheel -/

theorem not_prime_of_dvd {n d : Nat} (hd : d ∣ n) (h1 : 1 < d) (h2 : d < n) : ¬ n.Prime := by
  intro hp
  rcases hp.eq_one_or_self_of_dvd d hd with h | h <;> omega

/-- Every `i ≡ 5 [MOD 6]` with `5 ≤ i ≤ Nat.sqrt n` is visited by the loop. -/
theorem mem_wheelCandidates {n i : Nat} (h5 : 5 ≤ i) (hle : i ≤ Nat.sqrt n)
    (hmod : i % 6 = 5) : i ∈ wheelCandidates n := by
  have hs : ¬ (Nat.sqrt n < 5) := by omega
  rw [wheelCandidates, List.mem_range']
  refine ⟨(i - 5) / 6, ?_, ?_⟩
  · rw [numSteps, if_neg hs]; omega
  · omega

/-- Conversely, every value visited by the loop lies in `[5, Nat.sqrt n]`. -/
theorem wheelCandidates_bounds {n i : Nat} (h : i ∈ wheelCandidates n) :
    5 ≤ i ∧ i ≤ Nat.sqrt n := by
  rw [wheelCandidates, List.mem_range'] at h
  obtain ⟨j, hj, rfl⟩ := h
  rw [numSteps] at hj
  by_cases hs : Nat.sqrt n < 5
  · rw [if_pos hs] at hj; omega
  · rw [if_neg hs] at hj; omega

/-! ## Correctness of the algorithm -/

/-- The wheel algorithm decides primality on `Nat`. -/
theorem isPrimeNat_eq_true_iff (n : Nat) : isPrimeNat n = true ↔ Nat.Prime n := by
  rw [isPrimeNat]
  by_cases h1 : n ≤ 1
  · rw [if_pos h1]
    simp only [Bool.false_eq_true, false_iff]
    intro hp; have := hp.two_le; omega
  rw [if_neg h1]
  by_cases h3 : n ≤ 3
  · rw [if_pos h3]
    simp only [true_iff]
    interval_cases n
    · exact Nat.prime_two
    · exact Nat.prime_three
  rw [if_neg h3]
  by_cases h23 : (n % 2 == 0 || n % 3 == 0) = true
  · rw [if_pos h23]
    simp only [Bool.false_eq_true, false_iff]
    simp only [Bool.or_eq_true, beq_iff_eq] at h23
    rcases h23 with h | h
    · exact not_prime_of_dvd (Nat.dvd_of_mod_eq_zero h) (by omega) (by omega)
    · exact not_prime_of_dvd (Nat.dvd_of_mod_eq_zero h) (by omega) (by omega)
  rw [if_neg h23]
  simp only [Bool.or_eq_true, beq_iff_eq, not_or] at h23
  obtain ⟨h2, h3'⟩ := h23
  -- Now `n ≥ 4`, `n % 2 ≠ 0`, `n % 3 ≠ 0`, hence `n ≥ 5`.
  have hn5 : 5 ≤ n := by omega
  have hsq_lt : Nat.sqrt n < n := Nat.sqrt_lt_self (by omega)
  constructor
  · -- the loop found no divisor ⟹ `n` is prime
    intro hall
    rw [List.all_eq_true] at hall
    rw [Nat.prime_def_le_sqrt]
    refine ⟨by omega, ?_⟩
    intro m hm2 hms hmd
    -- take the least prime factor of `m`
    set p := m.minFac with hpdef
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpm : p ∣ m := Nat.minFac_dvd m
    have hpn : p ∣ n := hpm.trans hmd
    have hple : p ≤ m := Nat.le_of_dvd (by omega) hpm
    have hpsq : p ≤ Nat.sqrt n := le_trans hple hms
    have hpz : n % p = 0 := by
      first
      | exact (Nat.mod_eq_zero_iff_dvd hp.pos).mpr hpn
      | exact Nat.mod_eq_zero_of_dvd hpn
    have hp2 : p % 2 ≠ 0 := by
      intro hc
      have hd : (2 : Nat) ∣ n := dvd_trans (Nat.dvd_of_mod_eq_zero hc) hpn
      omega
    have hp3 : p % 3 ≠ 0 := by
      intro hc
      have hd : (3 : Nat) ∣ n := dvd_trans (Nat.dvd_of_mod_eq_zero hc) hpn
      omega
    have hpge2 : 2 ≤ p := hp.two_le
    have hp5 : 5 ≤ p := by omega
    have h6 : p % 6 = 1 ∨ p % 6 = 5 := by omega
    rcases h6 with h6 | h6
    · -- `p ≡ 1 [MOD 6]`: `p` is reached as `i + 2` for `i = p - 2`
      have hmem : (p - 2) ∈ wheelCandidates n :=
        mem_wheelCandidates (by omega) (by omega) (by omega)
      have hchk := hall _ hmem
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne,
        ne_eq] at hchk
      have he : p - 2 + 2 = p := by omega
      rw [he] at hchk
      exact hchk.2 hpz
    · -- `p ≡ 5 [MOD 6]`: `p` is itself a loop value `i`
      have hmem : p ∈ wheelCandidates n :=
        mem_wheelCandidates (by omega) hpsq h6
      have hchk := hall _ hmem
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne,
        ne_eq] at hchk
      exact hchk.1 hpz
  · -- `n` prime ⟹ every candidate check succeeds
    intro hp
    rw [List.all_eq_true]
    intro i hi
    obtain ⟨hi5, hile⟩ := wheelCandidates_bounds hi
    have hsq5 : 5 ≤ Nat.sqrt n := le_trans hi5 hile
    have hsqle : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
    have hbig : Nat.sqrt n + 2 < n := by nlinarith
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
    constructor
    · intro hc
      exact not_prime_of_dvd (Nat.dvd_of_mod_eq_zero hc) (by omega) (by omega) hp
    · intro hc
      exact not_prime_of_dvd (Nat.dvd_of_mod_eq_zero hc) (by omega) (by omega) hp

/-! ## Properties and theorems -/

/-- Main property: on non-negative inputs `is_prime` decides primality. -/
def isPrime_correct_prop (n : Int) : Prop :=
  Pre n → (isPrime n = true ↔ Nat.Prime n.toNat)

theorem isPrime_correct_thm (n : Int) : isPrime_correct_prop n := by
  intro _
  exact isPrimeNat_eq_true_iff n.toNat

/-- Elementary restatement: the result is `true` exactly when `n > 1` and `n` has no
divisor other than `1` and itself — the definition quoted in the Python docstring. -/
def isPrime_divisor_prop (n : Int) : Prop :=
  Pre n → (isPrime n = true ↔ (2 ≤ n.toNat ∧ ∀ d : Nat, d ∣ n.toNat → d = 1 ∨ d = n.toNat))

theorem isPrime_divisor_thm (n : Int) : isPrime_divisor_prop n := by
  intro h
  rw [isPrime_correct_thm n h]
  constructor
  · intro hp; exact ⟨hp.two_le, fun d hd => hp.eq_one_or_self_of_dvd d hd⟩
  · rintro ⟨h2, hd⟩
    first
    | exact Nat.prime_def_lt''.mpr ⟨h2, hd⟩
    | exact Nat.prime_def.mpr ⟨h2, hd⟩

/-- `0` and `1` are not prime (the Python edge cases). -/
def isPrime_le_one_prop (n : Int) : Prop :=
  Pre n → n ≤ 1 → isPrime n = false

theorem isPrime_le_one_thm (n : Int) : isPrime_le_one_prop n := by
  intro h h1
  have : n.toNat ≤ 1 := by omega
  simp [isPrime, isPrimeNat, this]

/-- The small primes handled by the `n ≤ 3` shortcut. -/
def isPrime_small_prop : Prop :=
  isPrime 0 = false ∧ isPrime 1 = false ∧ isPrime 2 = true ∧ isPrime 3 = true ∧
    isPrime 4 = false

theorem isPrime_small_thm : isPrime_small_prop := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- On valid inputs the total model returns `ok` with the functional result. -/
def isPrime_ok_prop (n : Int) : Prop :=
  Pre n → isPrimeE n = Except.ok (isPrime n)

theorem isPrime_ok_thm (n : Int) : isPrime_ok_prop n := by
  intro h
  simp [isPrimeE, Pre] at h ⊢
  exact h

/-- On invalid inputs the Python code raises `ValueError`. -/
def isPrime_error_prop (n : Int) : Prop :=
  ¬ Pre n → isPrimeE n = Except.error "Input must be non-negative integer"

theorem isPrime_error_thm (n : Int) : isPrime_error_prop n := by
  intro h
  simp [isPrimeE, Pre] at h ⊢
  omega

/-! ## Post-condition and overall correctness -/

def Post_prop (n : Int) : Prop :=
  isPrime_correct_prop n ∧ isPrime_divisor_prop n ∧ isPrime_le_one_prop n ∧
    isPrime_ok_prop n ∧ isPrime_error_prop n ∧ isPrime_small_prop

/-- Correctness: the precondition implies the post-condition. -/
theorem isPrime_spec (n : Int) : Pre n → Post_prop n := by
  intro _
  exact ⟨isPrime_correct_thm n, isPrime_divisor_thm n, isPrime_le_one_thm n,
    isPrime_ok_thm n, isPrime_error_thm n, isPrime_small_thm⟩

/-! ## Imperative implementation -/

/-- The `for i in range(5, int(sqrt(n)) + 1, 6)` loop of the Python source, written with
a mutable flag. -/
def wheelScan (m : Nat) (l : List Nat) : Bool := Id.run do
  let mut res := true
  for i in l do
    if m % i == 0 || m % (i + 2) == 0 then
      res := false
  return res

/-- Imperative transcription of the Python body, with a mutable flag updated inside the
`for i in range(5, int(sqrt(n)) + 1, 6)` loop. -/
def isPrimeImp (n : Int) : Bool := Id.run do
  let m := n.toNat
  if m ≤ 1 then
    return false
  if m ≤ 3 then
    return true
  if m % 2 == 0 || m % 3 == 0 then
    return false
  let mut res := true
  for i in wheelCandidates m do
    if m % i == 0 || m % (i + 2) == 0 then
      res := false
  return res

/-! ## Imperative tests -/

example : isPrimeImp 7 = true := by native_decide
example : isPrimeImp 0 = false := by native_decide
example : isPrimeImp 2 = true := by native_decide
example : isPrimeImp 4 = false := by native_decide
example : isPrimeImp 25 = false := by native_decide
example : isPrimeImp 7919 = true := by native_decide

#eval isPrimeImp 7
#eval (List.range 30).filter (fun n => isPrimeImp (n : Int))

/-! ## Equivalence of the two implementations -/

/-- The mutable-flag loop, run from an arbitrary starting value, computes the
conjunction of all the divisibility checks. -/
theorem wheelScan_aux (m : Nat) : ∀ (l : List Nat) (b : Bool),
    (Id.run (do
      let mut res := b
      for i in l do
        if m % i == 0 || m % (i + 2) == 0 then
          res := false
      return res))
      = (b && l.all fun i => !(m % i == 0) && !(m % (i + 2) == 0)) := by
  intro l
  induction l with
  | nil => intro b; cases b <;> rfl
  | cons a as ih =>
    intro b
    by_cases h : m % a = 0 ∨ m % (a + 2) = 0
    · have e : (Id.run (do
          let mut res := b
          for i in a :: as do
            if m % i == 0 || m % (i + 2) == 0 then
              res := false
          return res)) = (Id.run (do
          let mut res := false
          for i in as do
            if m % i == 0 || m % (i + 2) == 0 then
              res := false
          return res)) := by
        simp [Id.run, List.forIn_cons, h]
      rw [e, ih]
      rcases h with h | h <;> simp [h]
    · push_neg at h
      have e : (Id.run (do
          let mut res := b
          for i in a :: as do
            if m % i == 0 || m % (i + 2) == 0 then
              res := false
          return res)) = (Id.run (do
          let mut res := b
          for i in as do
            if m % i == 0 || m % (i + 2) == 0 then
              res := false
          return res)) := by
        simp [Id.run, List.forIn_cons, h.1, h.2]
      rw [e, ih]
      have h1 : (m % a == 0) = false := beq_eq_false_iff_ne.mpr h.1
      have h2 : (m % (a + 2) == 0) = false := beq_eq_false_iff_ne.mpr h.2
      simp [h1, h2]

theorem wheelScan_eq (m : Nat) (l : List Nat) :
    wheelScan m l = l.all fun i => !(m % i == 0) && !(m % (i + 2) == 0) := by
  rw [wheelScan, wheelScan_aux m l true, Bool.true_and]

/-- Equivalence theorem: the imperative implementation agrees with the functional one. -/
theorem isPrimeImp_eq_isPrime (n : Int) : isPrimeImp n = isPrime n := by
  show isPrimeImp n = isPrimeNat n.toNat
  rw [isPrimeImp, isPrimeNat]
  simp only [Id.run]
  split_ifs with h1 h2 h3
  · rfl
  · rfl
  · rfl
  · exact wheelScan_eq n.toNat (wheelCandidates n.toNat)

/-- Consequently the imperative version also meets the specification. -/
theorem isPrimeImp_correct (n : Int) (h : Pre n) :
    isPrimeImp n = true ↔ Nat.Prime n.toNat := by
  rw [isPrimeImp_eq_isPrime]
  exact isPrime_correct_thm n h

end «23_is_prime»
