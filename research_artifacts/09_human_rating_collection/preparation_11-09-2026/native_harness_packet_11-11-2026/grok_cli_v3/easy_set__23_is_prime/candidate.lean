import Mathlib

/-!
# 23_is_prime

Lean 4 formalization of a 6k±1 primality test.

The Python program rejects negative inputs with `ValueError` and, for a
non-negative integer `n`, returns whether `n` is prime. `0` and `1` are not
prime. The search bound `int(math.sqrt(n))` is the mathematical integer square
root (`Nat.sqrt`): the procedure is the number-theoretic trial up to `√n`, not
an IEEE-754 specification. Candidates of the form `6k ± 1` are exactly the
integers `i ≥ 5` with `i % 6 = 5`, together with `i + 2`.
-/

namespace «23_is_prime»

/-- Error message used when the input is negative. -/
def errMsg : String := "Input must be non-negative integer"

/--
Trial division from `i`, stepping by 6, while `i * i ≤ n`.
`i` and `i + 2` are the `6k − 1` and `6k + 1` candidates.
-/
def trialFrom (n i : Nat) : Bool :=
  if i * i ≤ n then
    if n % i == 0 || n % (i + 2) == 0 then
      false
    else
      trialFrom n (i + 6)
  else
    true
termination_by Nat.sqrt n + 6 - i
decreasing_by
  simp_wf
  have hle : i ≤ Nat.sqrt n := Nat.le_sqrt.mpr ‹i * i ≤ n›
  exact Nat.sub_lt_sub_right hle (Nat.lt_add_of_pos_right (by decide : 0 < 6))

lemma trialFrom_div (n i : Nat) (hle : i * i ≤ n)
    (hdiv : (n % i == 0 || n % (i + 2) == 0) = true) :
    trialFrom n i = false := by
  rw [trialFrom.eq_1]
  simp only [if_pos hle, if_pos hdiv]

lemma trialFrom_rec (n i : Nat) (hle : i * i ≤ n)
    (hnd : ¬ (n % i == 0 || n % (i + 2) == 0) = true) :
    trialFrom n i = trialFrom n (i + 6) := by
  rw [trialFrom.eq_1]
  simp only [if_pos hle, if_neg hnd]

lemma trialFrom_stop (n i : Nat) (hgt : ¬ i * i ≤ n) :
    trialFrom n i = true := by
  rw [trialFrom.eq_1]
  simp only [if_neg hgt]

lemma add6_mod (i : Nat) (h : i % 6 = 5) : (i + 6) % 6 = 5 := by
  have : (i + 6) % 6 = (i % 6 + 6 % 6) % 6 := Nat.add_mod _ _ _
  simpa [h, Nat.mod_self] using this

lemma next_wheel {x j : Nat} (hx : x % 6 = 5) (hj : j % 6 = 5) (hle : x ≤ j) (hne : x ≠ j) :
    x + 6 ≤ j := by
  have hcong : x ≡ j [MOD 6] := by
    simp [Nat.ModEq, hx, hj]
  have hdvd : 6 ∣ j - x := (Nat.modEq_iff_dvd' hle).1 hcong
  have hpos : 0 < j - x := Nat.sub_pos_of_lt (lt_of_le_of_ne hle hne)
  have hge : 6 ≤ j - x := Nat.le_of_dvd hpos hdvd
  omega

lemma forall_wheel_step (n x : Nat) (hx : x % 6 = 5) (_hxle : x * x ≤ n)
    (hclean : n % x ≠ 0 ∧ n % (x + 2) ≠ 0) :
    (∀ j, x ≤ j → j * j ≤ n → j % 6 = 5 → n % j ≠ 0 ∧ n % (j + 2) ≠ 0) ↔
      (∀ j, x + 6 ≤ j → j * j ≤ n → j % 6 = 5 → n % j ≠ 0 ∧ n % (j + 2) ≠ 0) := by
  constructor
  · intro hall j hj hjsq hjmod
    exact hall j (le_trans (Nat.le_add_right x 6) hj) hjsq hjmod
  · intro hall j hj hjsq hjmod
    by_cases heq : j = x
    · simpa [heq] using hclean
    · exact hall j (next_wheel hx hjmod hj (Ne.symm heq)) hjsq hjmod

lemma div_or_of_bool (n i : Nat) (hdiv : (n % i == 0 || n % (i + 2) == 0) = true) :
    n % i = 0 ∨ n % (i + 2) = 0 := by
  simpa [Bool.or_eq_true, beq_iff_eq] using hdiv

lemma not_div_and_of_bool (n i : Nat) (hnd : ¬ (n % i == 0 || n % (i + 2) == 0) = true) :
    n % i ≠ 0 ∧ n % (i + 2) ≠ 0 := by
  have hf : (n % i == 0 || n % (i + 2) == 0) = false := by
    simpa [Bool.not_eq_true] using hnd
  have hs : (n % i == 0) = false ∧ (n % (i + 2) == 0) = false := by
    simpa [Bool.or_eq_false_iff] using hf
  constructor
  · intro h
    have : (n % i == 0) = true := (beq_iff_eq).mpr h
    simp [this] at hs
  · intro h
    have : (n % (i + 2) == 0) = true := (beq_iff_eq).mpr h
    simp [this] at hs

theorem trialFrom_true_iff (n : Nat) :
    ∀ i, i % 6 = 5 →
      (trialFrom n i = true ↔
        ∀ j, i ≤ j → j * j ≤ n → j % 6 = 5 → n % j ≠ 0 ∧ n % (j + 2) ≠ 0) := by
  let motive : Nat → Prop := fun i =>
    i % 6 = 5 →
      (trialFrom n i = true ↔
        ∀ j, i ≤ j → j * j ≤ n → j % 6 = 5 → n % j ≠ 0 ∧ n % (j + 2) ≠ 0)
  intro i hi
  refine trialFrom.induct n motive ?case1 ?case2 ?case3 i hi
  · intro x hle hdiv hx
    have ht : trialFrom n x = false := trialFrom_div n x hle hdiv
    rw [ht]
    constructor
    · intro h
      exact absurd h Bool.false_ne_true
    · intro hall
      have hbad := hall x (le_refl _) hle hx
      rcases div_or_of_bool n x hdiv with h0 | h0
      · exact absurd h0 hbad.1
      · exact absurd h0 hbad.2
  · intro x hle hnd ih hx
    have hx6 : (x + 6) % 6 = 5 := add6_mod x hx
    have ih' := ih hx6
    have hrec : trialFrom n x = trialFrom n (x + 6) := trialFrom_rec n x hle hnd
    have hclean := not_div_and_of_bool n x hnd
    rw [hrec, ih', forall_wheel_step n x hx hle hclean]
  · intro x hgt hx
    have ht : trialFrom n x = true := trialFrom_stop n x hgt
    simp only [ht, true_iff]
    intro j hjle hjsq _hjmod
    exfalso
    have hxx : x * x ≤ j * j := Nat.mul_le_mul hjle hjle
    have : x * x ≤ n := le_trans hxx hjsq
    exact (Nat.lt_of_not_le hgt).not_ge this

/-- Functional 6k±1 primality test on a non-negative integer. -/
def isPrime (n : Nat) : Bool :=
  if n ≤ 1 then false
  else if n ≤ 3 then true
  else if n % 2 == 0 || n % 3 == 0 then false
  else trialFrom n 5

/--
Python entry point. Negative integers raise `ValueError`; every other `Int`
is a non-negative integer and is tested by `isPrime`.
-/
def isPrimeEx (n : Int) : Except String Bool :=
  if n < 0 then
    .error errMsg
  else
    .ok (isPrime n.toNat)

/-- Unit tests from the Python docstring and `check`. -/
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
example : isPrimeEx (-1) = Except.error errMsg := by
  simp [isPrimeEx]
example : isPrimeEx 0 = Except.ok false := by
  simp [isPrimeEx]
  native_decide
example : isPrimeEx 7 = Except.ok true := by
  simp [isPrimeEx]
  native_decide

#eval isPrime 17
#eval isPrimeEx (-5)
#eval (List.range 20).map isPrime

/-- Pre-condition: the input is a non-negative integer (`isinstance(n, int) and n ≥ 0`). -/
def Pre (n : Int) : Prop := 0 ≤ n

lemma mod6_residue (m : Nat) (h2 : ¬ 2 ∣ m) (h3 : ¬ 3 ∣ m) : m % 6 = 1 ∨ m % 6 = 5 := by
  have hlt : m % 6 < 6 := Nat.mod_lt _ (by decide)
  interval_cases hmod : m % 6
  · have h := Nat.mod_mod_of_dvd m (show 2 ∣ 6 by decide)
    simp [hmod] at h
    exact (h2 (Nat.dvd_of_mod_eq_zero h.symm)).elim
  · exact Or.inl rfl
  · have h := Nat.mod_mod_of_dvd m (show 2 ∣ 6 by decide)
    simp [hmod] at h
    exact (h2 (Nat.dvd_of_mod_eq_zero h.symm)).elim
  · have h := Nat.mod_mod_of_dvd m (show 3 ∣ 6 by decide)
    simp [hmod] at h
    exact (h3 (Nat.dvd_of_mod_eq_zero h.symm)).elim
  · have h := Nat.mod_mod_of_dvd m (show 2 ∣ 6 by decide)
    simp [hmod] at h
    exact (h2 (Nat.dvd_of_mod_eq_zero h.symm)).elim
  · exact Or.inr rfl

lemma sq_pred_two_gt {n : Nat} (hn : 5 ≤ n) : n < (n - 2) * (n - 2) := by
  have h2 : 2 ≤ n := by omega
  set k : Nat := n - 2
  have hn' : k + 2 = n := by simpa [k] using Nat.sub_add_cancel h2
  have hk : 3 ≤ k := by omega
  rw [← hn']
  have hs : k - 1 + 1 = k := Nat.sub_add_cancel (by omega : 1 ≤ k)
  have hmul : k * (k - 1) + k = k * k := by
    calc
      k * (k - 1) + k = k * (k - 1) + k * 1 := by rw [Nat.mul_one]
      _ = k * ((k - 1) + 1) := by rw [← Nat.mul_add]
      _ = k * k := by rw [hs]
  have htwo : 2 ≤ k - 1 := by omega
  have hge : 2 * k ≤ (k - 1) * k := Nat.mul_le_mul_right k htwo
  have hsum : 2 * k + k ≤ k * k := by
    rw [← hmul]
    simpa [Nat.mul_comm] using Nat.add_le_add_right hge k
  have h3k : 2 * k + k = 3 * k := by
    calc
      2 * k + k = k * 2 + k * 1 := by simp [Nat.mul_comm, Nat.mul_one]
      _ = k * (2 + 1) := by rw [← Nat.mul_add]
      _ = 3 * k := by simp [Nat.mul_comm]
  have hlt : k + 2 < 3 * k := by
    have h2k : 3 ≤ 2 * k := by
      have : 2 * 2 ≤ 2 * k := Nat.mul_le_mul_left 2 (by omega : 2 ≤ k)
      omega
    omega
  exact lt_of_lt_of_le hlt (by simpa [h3k] using hsum)

lemma mod_sub_two_of_one {m : Nat} (h : m % 6 = 1) (hm : 7 ≤ m) : (m - 2) % 6 = 5 := by
  have hq : 1 ≤ m / 6 := by
    by_contra hq
    have hq0 : m / 6 = 0 := by omega
    have hdiv : 6 * (m / 6) + m % 6 = m := Nat.div_add_mod m 6
    rw [hq0, h] at hdiv
    simp at hdiv
    omega
  have hdiv : 6 * (m / 6) + m % 6 = m := Nat.div_add_mod m 6
  have hrepr : m = 6 * (m / 6) + 1 := by
    rw [h] at hdiv
    exact hdiv.symm
  have hsub : m - 2 = 5 + (m / 6 - 1) * 6 := by omega
  rw [hsub]
  simp [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (show 5 < 6 by decide)]

lemma not_mod_two_or_three {n : Nat}
    (h23 : ¬ (n % 2 == 0 || n % 3 == 0) = true) : n % 2 ≠ 0 ∧ n % 3 ≠ 0 := by
  have hf : (n % 2 == 0 || n % 3 == 0) = false := by
    simpa [Bool.not_eq_true] using h23
  have hs : (n % 2 == 0) = false ∧ (n % 3 == 0) = false := by
    simpa [Bool.or_eq_false_iff] using hf
  constructor
  · intro h
    have : (n % 2 == 0) = true := (beq_iff_eq).mpr h
    simp [this] at hs
  · intro h
    have : (n % 3 == 0) = true := (beq_iff_eq).mpr h
    simp [this] at hs

lemma or_mod_two_or_three {n : Nat}
    (h23 : (n % 2 == 0 || n % 3 == 0) = true) : n % 2 = 0 ∨ n % 3 = 0 := by
  simpa [Bool.or_eq_true, beq_iff_eq] using h23

/-- `isPrime` agrees with the mathematical definition of primality. -/
def isPrime_iff_prime_prop (n : Nat) : Prop :=
  isPrime n = true ↔ Nat.Prime n

theorem isPrime_iff_prime (n : Nat) : isPrime n = true ↔ Nat.Prime n := by
  unfold isPrime
  by_cases h1 : n ≤ 1
  · simp only [h1, ite_true]
    constructor
    · intro h
      exact absurd h Bool.false_ne_true
    · intro hp
      have := hp.two_le
      exfalso
      omega
  · simp only [h1, ite_false]
    by_cases h3 : n ≤ 3
    · simp only [h3, ite_true]
      have hn2 : 2 ≤ n := by omega
      interval_cases n
      · exact ⟨fun _ => Nat.prime_two, fun _ => trivial⟩
      · exact ⟨fun _ => Nat.prime_three, fun _ => trivial⟩
    · simp only [h3, ite_false]
      by_cases h23 : (n % 2 == 0 || n % 3 == 0) = true
      · simp only [h23, ite_true]
        constructor
        · intro h
          exact absurd h Bool.false_ne_true
        · intro hp
          rcases or_mod_two_or_three h23 with h2 | h3d
          · have hd : 2 ∣ n := Nat.dvd_of_mod_eq_zero h2
            rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> exfalso <;> omega
          · have hd : 3 ∣ n := Nat.dvd_of_mod_eq_zero h3d
            rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> exfalso <;> omega
      · have hclean := not_mod_two_or_three h23
        simp only [if_neg h23]
        rw [trialFrom_true_iff n 5 (by decide)]
        constructor
        · intro hall
          refine Nat.prime_def_le_sqrt.mpr ⟨by omega, ?_⟩
          intro m hm2 hmsq hmd
          have hsq : m * m ≤ n := Nat.le_sqrt.mp hmsq
          by_cases h2d : 2 ∣ m
          · exact hclean.1 (Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h2d hmd))
          · by_cases h3d : 3 ∣ m
            · exact hclean.2 (Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h3d hmd))
            · have hm5 : 5 ≤ m := by
                by_contra hlt
                have : m < 5 := lt_of_not_ge hlt
                interval_cases m
                · omega
                · omega
                · exact h2d (by decide)
              rcases mod6_residue m h2d h3d with hmod | hmod
              · have hm7 : 7 ≤ m := by
                  by_contra hlt
                  have hmset : m = 5 ∨ m = 6 := by omega
                  rcases hmset with rfl | rfl
                  · simp at hmod
                  · simp at hmod
                have hjmod : (m - 2) % 6 = 5 := mod_sub_two_of_one hmod hm7
                have hj5 : 5 ≤ m - 2 := by omega
                have hjsq : (m - 2) * (m - 2) ≤ n := by
                  have hle : m - 2 ≤ m := by omega
                  exact le_trans (Nat.mul_le_mul hle hle) hsq
                have hbad := hall (m - 2) hj5 hjsq hjmod
                have hadd : m - 2 + 2 = m := by omega
                have : n % m ≠ 0 := by simpa [hadd] using hbad.2
                exact this (Nat.mod_eq_zero_of_dvd hmd)
              · have hbad := hall m hm5 hsq hmod
                exact hbad.1 (Nat.mod_eq_zero_of_dvd hmd)
        · intro hp j h5 hjsq hjmod
          have hjle : j ≤ Nat.sqrt n := Nat.le_sqrt.mpr hjsq
          have hndj : ¬ j ∣ n := (Nat.prime_def_le_sqrt.mp hp).2 j (by omega) hjle
          have hneq1 : n % j ≠ 0 := fun h => hndj (Nat.dvd_of_mod_eq_zero h)
          have hn5 : 5 ≤ n := by omega
          have hbig := sq_pred_two_gt hn5
          have hjlt : j < n - 2 := by
            by_contra hge
            have hle2 : n - 2 ≤ j := by omega
            have : (n - 2) * (n - 2) ≤ j * j := Nat.mul_le_mul hle2 hle2
            exact Nat.lt_irrefl _ (lt_of_lt_of_le hbig (le_trans this hjsq))
          have hltn : j + 2 < n := by omega
          have hnd2 : ¬ (j + 2) ∣ n := by
            intro hd
            rcases hp.eq_one_or_self_of_dvd (j + 2) hd with h | h
            · omega
            · omega
          have hneq2 : n % (j + 2) ≠ 0 := fun h => hnd2 (Nat.dvd_of_mod_eq_zero h)
          exact ⟨hneq1, hneq2⟩

theorem isPrime_iff_prime_thm (n : Nat) : isPrime_iff_prime_prop n :=
  isPrime_iff_prime n

/-- `0` and `1` are not prime. -/
def le_one_not_prime_prop (n : Nat) : Prop :=
  n ≤ 1 → isPrime n = false

theorem le_one_not_prime_thm (n : Nat) : le_one_not_prime_prop n := by
  intro hn
  simp [isPrime, hn]

/-- Multiples of 2 or 3 that are greater than 3 are not prime. -/
def early_composite_prop (n : Nat) : Prop :=
  3 < n → (n % 2 = 0 ∨ n % 3 = 0) → isPrime n = false

theorem early_composite_thm (n : Nat) : early_composite_prop n := by
  intro hn hdiv
  have h1 : ¬ n ≤ 1 := by omega
  have h3 : ¬ n ≤ 3 := by omega
  have hb : (n % 2 == 0 || n % 3 == 0) = true := by
    rcases hdiv with h | h
    · simp [h, beq_iff_eq]
    · have : (n % 3 == 0) = true := (beq_iff_eq).mpr h
      simp [this]
  simp [isPrime, h1, h3, hb]

/-- A negative input raises `ValueError` with the Python message. -/
def error_on_negative_prop (n : Int) : Prop :=
  ¬ Pre n → isPrimeEx n = Except.error errMsg

theorem error_on_negative_thm (n : Int) : error_on_negative_prop n := by
  intro hn
  have hlt : n < 0 := not_le.mp hn
  simp [isPrimeEx, hlt]

/-- Post-condition: on a non-negative input the test succeeds and matches `Nat.Prime`. -/
def Post_prop (n : Int) : Prop :=
  isPrimeEx n = Except.ok (isPrime n.toNat) ∧ isPrime_iff_prime_prop n.toNat

/-! ## Property-based tests -/

example : (List.range 80).all (fun n => isPrime n == decide (Nat.Prime n)) = true := by
  native_decide

#eval Plausible.Testable.check (∀ n : Nat, isPrime n = decide (Nat.Prime n))
  { numInst := 25, maxSize := 40 : Plausible.Configuration }

example : (List.range 40).all (fun n => !decide (n ≤ 1) || isPrime n == false) = true := by
  native_decide

/-- Executable form of `error_on_negative_prop` on `-(k+1)`. -/
def checksError (k : Nat) : Bool :=
  match isPrimeEx (-(k : Int) - 1) with
  | .error m => m == errMsg
  | .ok _ => false

example : (List.range 30).all checksError = true := by
  native_decide

#eval Plausible.Testable.check (∀ k : Nat, checksError k = true)
  { numInst := 20, maxSize := 30 : Plausible.Configuration }

/-- Executable form of `Post_prop` on a non-negative integer. -/
def checksPost (n : Nat) : Bool :=
  match isPrimeEx (n : Int) with
  | .ok b => b == isPrime n && b == decide (Nat.Prime n)
  | .error _ => false

example : (List.range 50).all checksPost = true := by
  native_decide

#eval Plausible.Testable.check (∀ n : Nat, checksPost n = true)
  { numInst := 20, maxSize := 40 : Plausible.Configuration }

example : (List.range 60).all (fun n =>
    !decide (3 < n) || !((n % 2 == 0) || (n % 3 == 0)) || isPrime n == false) = true := by
  native_decide

/-- If the pre-condition holds, the post-condition holds. -/
theorem correctness_thm (n : Int) (hn : Pre n) : Post_prop n := by
  unfold Post_prop
  refine ⟨?ok, isPrime_iff_prime_thm n.toNat⟩
  unfold isPrimeEx
  have hlt : ¬ n < 0 := not_lt.mpr hn
  simp [hlt]

def bad (n i : Nat) : Bool :=
  (decide (5 ≤ i) && (i % 6 == 5)) && ((n % i == 0) || (n % (i + 2) == 0))

def step (n : Nat) (ok : Bool) (i : Nat) : Bool :=
  if (decide (i ≥ 5) && i % 6 == 5) = true then
    if (n % i == 0 || n % (i + 2) == 0) = true then false else ok
  else
    ok

def wheelClear (n : Nat) : Bool :=
  (List.range (n.sqrt + 1)).foldl (fun ok i => step n ok i) true

lemma step_eq_not_bad (n : Nat) (ok : Bool) (i : Nat) :
    step n ok i = (!bad n i && ok) := by
  unfold step bad
  cases h1 : decide (i ≥ 5) && (i % 6 == 5) <;>
    cases h2 : (n % i == 0 || n % (i + 2) == 0) <;>
      simp [h1, h2]

lemma foldl_step (n : Nat) (l : List Nat) (ok : Bool) :
    l.foldl (fun ok i => step n ok i) ok = (ok && l.all fun i => !bad n i) := by
  induction l generalizing ok with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons]
    rw [ih]
    rw [step_eq_not_bad]
    simp only [List.all_cons]
    cases ok <;> cases bad n a <;> simp

lemma not_bad_iff (n i : Nat) :
    (!bad n i) = true ↔ (5 ≤ i → i % 6 = 5 → n % i ≠ 0 ∧ n % (i + 2) ≠ 0) := by
  constructor
  · intro h h5 hmod
    have hb : bad n i = false := by simpa [Bool.not_eq_true] using h
    have h5b : decide (5 ≤ i) = true := by simpa using h5
    have hmb : (i % 6 == 5) = true := (beq_iff_eq).mpr hmod
    unfold bad at hb
    simp only [h5b, hmb, Bool.true_and] at hb
    have hpair : (n % i == 0) = false ∧ (n % (i + 2) == 0) = false := by
      simpa [Bool.or_eq_false_iff] using hb
    constructor
    · intro heq
      have : (n % i == 0) = true := (beq_iff_eq).mpr heq
      simp [this] at hpair
    · intro heq
      have : (n % (i + 2) == 0) = true := (beq_iff_eq).mpr heq
      simp [this] at hpair
  · intro h
    by_cases h5 : 5 ≤ i <;> by_cases hmod : i % 6 = 5
    · obtain ⟨ha, hb⟩ := h h5 hmod
      have ha' : (n % i == 0) = false := by simpa [beq_iff_eq, Bool.not_eq_true] using ha
      have hb' : (n % (i + 2) == 0) = false := by
        simpa [beq_iff_eq, Bool.not_eq_true] using hb
      have h5b : decide (5 ≤ i) = true := by simpa using h5
      have hmb : (i % 6 == 5) = true := (beq_iff_eq).mpr hmod
      have hor : ((n % i == 0) || (n % (i + 2) == 0)) = false := by
        simp [ha', hb', Bool.or_eq_false_iff]
      simp [bad, h5b, hmb, hor, Bool.not_eq_true]
    · have hmb : (i % 6 == 5) = false := by simpa [beq_iff_eq, Bool.not_eq_true] using hmod
      simp [bad, hmb, Bool.not_eq_true]
    · have h5b : decide (5 ≤ i) = false := by simpa using h5
      simp [bad, h5b, Bool.not_eq_true]
    · have h5b : decide (5 ≤ i) = false := by simpa using h5
      simp [bad, h5b, Bool.not_eq_true]

def isPrimeImp (n : Nat) : Bool := Id.run do
  let mut ok : Bool := true
  if n ≤ 1 then
    ok := false
  else if n ≤ 3 then
    ok := true
  else if n % 2 == 0 || n % 3 == 0 then
    ok := false
  else
    for i in List.range (Nat.sqrt n + 1) do
      if i ≥ 5 && i % 6 == 5 then
        if n % i == 0 || n % (i + 2) == 0 then
          ok := false
  return ok

/-- Imperative tests. -/
example : isPrimeImp 2 = true := by native_decide
example : isPrimeImp 0 = false := by native_decide
example : isPrimeImp 1 = false := by native_decide
example : isPrimeImp 4 = false := by native_decide
example : isPrimeImp 7 = true := by native_decide
example : isPrimeImp 9 = false := by native_decide
example : isPrimeImp 25 = false := by native_decide
example : isPrimeImp 97 = true := by native_decide
example : isPrimeImp 121 = false := by native_decide

#eval isPrimeImp 29
#eval isPrimeImp 1

lemma forIn_step (n : Nat) (l : List Nat) (ok : Bool) :
    (forIn (m := Id) l ok fun i r =>
        if (decide (i ≥ 5) && i % 6 == 5) = true then
          if (n % i == 0 || n % (i + 2) == 0) = true then ForInStep.yield false
          else ForInStep.yield r
        else ForInStep.yield r) =
      l.foldl (fun ok i => step n ok i) ok := by
  induction l generalizing ok with
  | nil =>
    simp only [List.forIn_nil, List.foldl_nil]
    rfl
  | cons a as ih =>
    simp only [List.forIn_cons, List.foldl_cons]
    by_cases h5 : (decide (a ≥ 5) && a % 6 == 5) = true
    · by_cases hd : (n % a == 0 || n % (a + 2) == 0) = true
      · have hstep : step n ok a = false := by simp [step, h5, hd]
        simp only [h5, hd, ite_true, bind, hstep, ih]
      · have hbf : (n % a == 0 || n % (a + 2) == 0) = false := by
          simpa [Bool.not_eq_true] using hd
        have hstep : step n ok a = ok := by simp [step, h5, hbf]
        simp only [h5, hbf, ite_true, if_neg Bool.false_ne_true, bind, hstep, ih]
    · have h5f : (decide (a ≥ 5) && a % 6 == 5) = false := by
        simpa [Bool.not_eq_true] using h5
      have hstep : step n ok a = ok := by simp [step, h5f]
      simp only [h5f, if_neg Bool.false_ne_true, bind, hstep, ih]

lemma imp_eq_wheel (n : Nat) :
    isPrimeImp n =
      if n ≤ 1 then false
      else if n ≤ 3 then true
      else if (n % 2 == 0 || n % 3 == 0) = true then false
      else wheelClear n := by
  unfold isPrimeImp wheelClear
  simp only [Id.run, bind, pure]
  by_cases h1 : n ≤ 1
  · simp only [h1, ite_true]
  · simp only [h1, ite_false]
    by_cases h3 : n ≤ 3
    · simp only [h3, ite_true]
    · simp only [h3, ite_false]
      by_cases h23 : (n % 2 == 0 || n % 3 == 0) = true
      · simp only [h23, ite_true]
      · simp only [h23, ite_false]
        exact forIn_step n (List.range (n.sqrt + 1)) true

lemma wheelClear_true_iff (n : Nat) :
    wheelClear n = true ↔
      ∀ j, 5 ≤ j → j * j ≤ n → j % 6 = 5 → n % j ≠ 0 ∧ n % (j + 2) ≠ 0 := by
  unfold wheelClear
  rw [foldl_step]
  simp only [Bool.true_and, List.all_eq_true]
  constructor
  · intro hall j h5 hjsq hjmod
    have hjle : j ≤ n.sqrt := Nat.le_sqrt.mpr hjsq
    have hmem : j ∈ List.range (n.sqrt + 1) := by
      simpa [List.mem_range] using Nat.lt_succ_of_le hjle
    exact (not_bad_iff n j).1 (hall j hmem) h5 hjmod
  · intro hall i hmem
    have hi : i < n.sqrt + 1 := by simpa [List.mem_range] using hmem
    rw [not_bad_iff]
    intro h5 hjmod
    exact hall i h5 (Nat.le_sqrt.mp (Nat.le_of_lt_succ hi)) hjmod

lemma bool_eq_of_eq_true_iff {a b : Bool} (h : (a = true) ↔ (b = true)) : a = b := by
  cases a <;> cases b <;> simp_all

lemma wheelClear_eq_trialFrom (n : Nat) : wheelClear n = trialFrom n 5 :=
  bool_eq_of_eq_true_iff <| by
    rw [wheelClear_true_iff, trialFrom_true_iff n 5 (by decide)]

/-- The functional test and the imperative loop agree on every natural number. -/
def equiv_prop (n : Nat) : Prop :=
  isPrime n = isPrimeImp n

theorem equiv_thm (n : Nat) : equiv_prop n := by
  unfold equiv_prop
  rw [imp_eq_wheel]
  unfold isPrime
  by_cases h1 : n ≤ 1
  · simp [h1]
  · by_cases h3 : n ≤ 3
    · simp [h1, h3]
    · by_cases h23 : (n % 2 == 0 || n % 3 == 0) = true
      · simp [h1, h3, h23]
      · simp [h1, h3, h23, if_neg h23, wheelClear_eq_trialFrom]

example : (List.range 60).all (fun n => isPrime n == isPrimeImp n) = true := by
  native_decide

#eval Plausible.Testable.check (∀ n : Nat, isPrime n = isPrimeImp n)
  { numInst := 20, maxSize := 40 : Plausible.Configuration }

end «23_is_prime»
