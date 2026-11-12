import Mathlib

/-!
# 20_MySumDigits: Sum of Digits in a Non-Negative Integer

This module formalizes the Python program that computes the sum of base-10 digits
of a non-negative integer `n`.

## Edge Cases and Specification
- Sum of digits of `0` is `0`.
- Single-digit non-negative integers (`0 <= n < 10`) return themselves.
- Input precondition `Pre n` requires `0 <= n`. The checked wrapper `mySumDigitsOpt`
  returns `none` when `n < 0` (modeling Python's `ValueError`).
- Includes functional implementations (`sumDigitsNat`, `mySumDigits`, `mySumDigitsOpt`),
  unit tests, precondition predicate, mathematical property propositions and kernel-checked
  proofs, postcondition conjunction, property-based tests (Plausible and bounded),
  correctness theorem (`Pre n -> Post_prop n`), imperative implementations using `Id.run do`
  with mutable state, imperative tests, and functional-imperative equivalence theorems.
-/

namespace MySumDigits

/-! ## 1. Functional Implementation -/

/-- Sum of base-10 digits of a natural number `n`. -/
def sumDigitsNat (n : Nat) : Nat :=
  if n = 0 then 0
  else n % 10 + sumDigitsNat (n / 10)

/-- Sum of base-10 digits of an integer `n` (returns `0` for `n <= 0`). -/
def mySumDigits (n : Int) : Int :=
  if n ≤ 0 then 0
  else (n % 10) + mySumDigits (n / 10)
termination_by n.toNat
decreasing_by omega

/-- Alias matching the Python function name `prog`. -/
abbrev prog (n : Int) : Int := mySumDigits n

/-- Checked version of `mySumDigits` that returns `none` if `n < 0`
    (modeling Python's `ValueError` on precondition violation). -/
def mySumDigitsOpt (n : Int) : Option Int :=
  if n < 0 then none
  else some (mySumDigits n)

/-! ## 2. Unit Tests -/

-- Basic unit test from Python `check`
example : mySumDigits 123 = 6 := by native_decide

-- Edge case: sum of digits of 0 is 0
example : mySumDigits 0 = 0 := by native_decide

-- Edge case: single-digit numbers return themselves
example : mySumDigits 1 = 1 := by native_decide
example : mySumDigits 5 = 5 := by native_decide
example : mySumDigits 9 = 9 := by native_decide

-- Additional multi-digit unit tests
example : mySumDigits 10 = 1 := by native_decide
example : mySumDigits 99 = 18 := by native_decide
example : mySumDigits 999 = 27 := by native_decide
example : mySumDigits 1000 = 1 := by native_decide
example : mySumDigits 123456789 = 45 := by native_decide

-- Checked version unit tests (including negative input raising error / returning `none`)
example : mySumDigitsOpt 123 = some 6 := by native_decide
example : mySumDigitsOpt 0 = some 0 := by native_decide
example : mySumDigitsOpt (-1) = none := by native_decide
example : mySumDigitsOpt (-42) = none := by native_decide

-- Nat version unit tests
example : sumDigitsNat 123 = 6 := by native_decide
example : sumDigitsNat 0 = 0 := by native_decide
example : sumDigitsNat 7 = 7 := by native_decide

#eval mySumDigits 123
#eval mySumDigits 0
#eval mySumDigits 9
#eval mySumDigits 987654321
#eval mySumDigitsOpt (-1)
#eval mySumDigitsOpt 123

/-! ## 3. Pre-condition Predicate -/

/-- Executable boolean precondition: `True` iff `n` is a non-negative integer. -/
def pre (n : Int) : Bool :=
  decide (0 ≤ n)

/-- Precondition predicate: `n` is a non-negative integer (`0 <= n`). -/
def Pre (n : Int) : Prop :=
  0 ≤ n

instance (n : Int) : Decidable (Pre n) :=
  inferInstanceAs (Decidable (0 ≤ n))

theorem pre_iff_Pre (n : Int) : pre n = true ↔ Pre n := by
  simp [pre, Pre]

/-! ## 4. Helper Lemmas & Property Propositions / Theorems -/

theorem sumDigitsNat_zero : sumDigitsNat 0 = 0 := by
  unfold sumDigitsNat; rfl

theorem sumDigitsNat_pos (n : Nat) (h : 0 < n) :
    sumDigitsNat n = n % 10 + sumDigitsNat (n / 10) := by
  rw [sumDigitsNat]
  have hne : n ≠ 0 := by omega
  simp [hne]

theorem sumDigitsNat_step (n : Nat) :
    sumDigitsNat n = n % 10 + sumDigitsNat (n / 10) := by
  by_cases h : n = 0
  · subst h; simp [sumDigitsNat_zero]
  · exact sumDigitsNat_pos n (by omega)

theorem sumDigitsNat_eq_digits_sum (n : Nat) :
    sumDigitsNat n = (Nat.digits 10 n).sum := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst hn; simp [sumDigitsNat_zero]
    · rw [sumDigitsNat_pos n (by omega)]
      rw [Nat.digits_def' (by decide : 1 < 10) (by omega : 0 < n)]
      simp only [List.sum_cons]
      rw [ih (n / 10) (Nat.div_lt_self (by omega) (by decide))]

theorem mySumDigits_nonpos (n : Int) (h : n ≤ 0) : mySumDigits n = 0 := by
  rw [mySumDigits]
  simp [h]

theorem mySumDigits_zero : mySumDigits 0 = 0 :=
  mySumDigits_nonpos 0 (by omega)

theorem mySumDigits_pos_step (n : Int) (h : 0 < n) :
    mySumDigits n = n % 10 + mySumDigits (n / 10) := by
  rw [mySumDigits]
  have hnotle : ¬ (n ≤ 0) := by omega
  simp [hnotle]

theorem mySumDigits_step (n : Int) (h : 0 ≤ n) :
    mySumDigits n = n % 10 + mySumDigits (n / 10) := by
  by_cases hn : n = 0
  · subst hn; simp [mySumDigits_zero]
  · exact mySumDigits_pos_step n (by omega)

theorem mySumDigits_eq_sumDigitsNat (n : Int) (h : 0 ≤ n) :
    mySumDigits n = Int.ofNat (sumDigitsNat n.toNat) := by
  induction h_eq : n.toNat using Nat.strong_induction_on generalizing n with
  | h k ih =>
    by_cases hn : n ≤ 0
    · have hn0 : n = 0 := by omega
      subst hn0; subst h_eq; simp [mySumDigits_zero, sumDigitsNat_zero]
    · rw [mySumDigits]
      simp only [hn, ↓reduceIte]
      have hk : 0 < k := by omega
      rw [sumDigitsNat_pos k hk]
      have hdiv_nonneg : 0 ≤ n / 10 := by omega
      have hdiv_toNat : (n / 10).toNat = k / 10 := by omega
      rw [ih (k / 10) (Nat.div_lt_self hk (by decide)) (n / 10) hdiv_nonneg hdiv_toNat]
      simp only [Int.ofNat_eq_coe, Nat.cast_add]
      omega

/-- Property 1: Non-negativity of the digit sum. -/
def nonneg_prop (n : Int) : Prop :=
  0 ≤ mySumDigits n

theorem nonneg_thm (n : Int) (_h : Pre n) : nonneg_prop n := by
  unfold nonneg_prop
  clear _h
  induction h_eq : n.toNat using Nat.strong_induction_on generalizing n with
  | h k ih =>
    by_cases hn : n ≤ 0
    · rw [mySumDigits_nonpos n hn]
    · rw [mySumDigits_pos_step n (by omega)]
      have hrec : 0 ≤ mySumDigits (n / 10) :=
        ih (n / 10).toNat (by omega) (n / 10) rfl
      omega

/-- Property 2: Single-digit non-negative integers return themselves. -/
def single_digit_prop (n : Int) : Prop :=
  n < 10 → mySumDigits n = n

theorem single_digit_thm (n : Int) (h : Pre n) : single_digit_prop n := by
  unfold Pre at h
  intro h10
  rw [mySumDigits_step n h]
  have hdiv : n / 10 = 0 := by omega
  have hmod : n % 10 = n := by omega
  rw [hdiv, hmod, mySumDigits_zero]
  omega

/-- Property 3: Strict positivity of the digit sum for positive integers. -/
def pos_prop (n : Int) : Prop :=
  0 < n → 0 < mySumDigits n

theorem pos_thm (n : Int) (_h : Pre n) : pos_prop n := by
  clear _h
  intro hpos
  induction h_eq : n.toNat using Nat.strong_induction_on generalizing n with
  | h k ih =>
    by_cases h10 : n < 10
    · rw [single_digit_thm n (by unfold Pre; omega) h10]
      exact hpos
    · rw [mySumDigits_pos_step n hpos]
      have hdiv_pos : 0 < n / 10 := by omega
      have hrec : 0 < mySumDigits (n / 10) :=
        ih (n / 10).toNat (by omega) (n / 10) hdiv_pos rfl
      omega

/-- Property 4: Sum of digits is `0` iff `n = 0` (for non-negative `n`). -/
def zero_prop (n : Int) : Prop :=
  (n = 0 → mySumDigits n = 0) ∧ (mySumDigits n = 0 ↔ n = 0)

theorem zero_thm (n : Int) (h : Pre n) : zero_prop n := by
  refine ⟨fun h0 => by subst h0; exact mySumDigits_zero, ?_⟩
  constructor
  · intro hsum
    by_contra hne
    have hnp : 0 < n := by unfold Pre at h; omega
    have hpos : 0 < mySumDigits n := pos_thm n h hnp
    omega
  · intro h0
    subst h0; exact mySumDigits_zero

/-- Property 5: Base-10 step recurrence `mySumDigits n = n % 10 + mySumDigits (n / 10)`. -/
def recurrence_prop (n : Int) : Prop :=
  mySumDigits n = n % 10 + mySumDigits (n / 10)

theorem recurrence_thm (n : Int) (h : Pre n) : recurrence_prop n :=
  mySumDigits_step n h

/-- Property 6: Upper bound `mySumDigits n <= n`. -/
def upper_bound_prop (n : Int) : Prop :=
  mySumDigits n ≤ n

theorem upper_bound_thm (n : Int) (h : Pre n) : upper_bound_prop n := by
  unfold upper_bound_prop
  unfold Pre at h
  induction h_eq : n.toNat using Nat.strong_induction_on generalizing n with
  | h k ih =>
    by_cases hn0 : n = 0
    · subst hn0; simp [mySumDigits_zero]
    · rw [mySumDigits_pos_step n (by omega)]
      have hrec : mySumDigits (n / 10) ≤ n / 10 :=
        ih (n / 10).toNat (by omega) (n / 10) (by omega) rfl
      omega

/-- Property 7: Multi-digit numbers (`n >= 10`) have digit sum strictly less than `n`. -/
def strict_lt_prop (n : Int) : Prop :=
  10 ≤ n → mySumDigits n < n

theorem strict_lt_thm (n : Int) (_h : Pre n) : strict_lt_prop n := by
  intro h10
  rw [mySumDigits_pos_step n (by omega)]
  have hrec : mySumDigits (n / 10) ≤ n / 10 := upper_bound_thm (n / 10) (by unfold Pre; omega)
  omega

/-- Property 8: Fixed-point characterization (`mySumDigits n = n <-> n < 10`). -/
def fixed_point_prop (n : Int) : Prop :=
  mySumDigits n = n ↔ n < 10

theorem fixed_point_thm (n : Int) (h : Pre n) : fixed_point_prop n := by
  unfold fixed_point_prop
  unfold Pre at h
  constructor
  · intro heq
    by_contra hge
    have hlt : mySumDigits n < n := strict_lt_thm n h (by omega)
    omega
  · intro hlt
    exact single_digit_thm n h hlt

/-- Property 9: Lower bound by the least significant digit (`n % 10 <= mySumDigits n`). -/
def lower_bound_prop (n : Int) : Prop :=
  n % 10 ≤ mySumDigits n

theorem lower_bound_thm (n : Int) (h : Pre n) : lower_bound_prop n := by
  unfold lower_bound_prop
  unfold Pre at h
  rw [mySumDigits_step n h]
  have hnonneg : 0 ≤ mySumDigits (n / 10) := nonneg_thm (n / 10) (by unfold Pre; omega)
  omega

/-- Property 10: Appending a base-10 digit `d` (`0 <= d < 10`) adds `d` to the digit sum. -/
def append_digit_prop (n : Int) : Prop :=
  ∀ d : Int, 0 ≤ d → d < 10 → mySumDigits (10 * n + d) = mySumDigits n + d

theorem append_digit_thm (n : Int) (h : Pre n) : append_digit_prop n := by
  unfold Pre at h
  intro d hd0 hd10
  rw [mySumDigits_step (10 * n + d) (by omega)]
  have hmod : (10 * n + d) % 10 = d := by omega
  have hdiv : (10 * n + d) / 10 = n := by omega
  rw [hmod, hdiv]
  omega

/-- Property 11: Multiplying by 10 preserves the sum of digits (`mySumDigits (10 * n) = mySumDigits n`). -/
def mul_ten_prop (n : Int) : Prop :=
  mySumDigits (10 * n) = mySumDigits n

theorem mul_ten_thm (n : Int) (h : Pre n) : mul_ten_prop n := by
  unfold mul_ten_prop
  have happ := append_digit_thm n h 0 (by omega) (by omega)
  simp only [add_zero] at happ
  exact happ

/-- Property 12: Congruence modulo 9 (casting out nines: `mySumDigits n % 9 = n % 9`). -/
def mod_nine_prop (n : Int) : Prop :=
  mySumDigits n % 9 = n % 9

theorem mod_nine_thm (n : Int) (h : Pre n) : mod_nine_prop n := by
  unfold mod_nine_prop
  unfold Pre at h
  induction h_eq : n.toNat using Nat.strong_induction_on generalizing n with
  | h k ih =>
    by_cases hn0 : n = 0
    · subst hn0; simp [mySumDigits_zero]
    · rw [mySumDigits_pos_step n (by omega)]
      have hrec : mySumDigits (n / 10) % 9 = (n / 10) % 9 :=
        ih (n / 10).toNat (by omega) (n / 10) (by omega) rfl
      omega

/-- Property 13: Congruence modulo 3 (`mySumDigits n % 3 = n % 3`). -/
def mod_three_prop (n : Int) : Prop :=
  mySumDigits n % 3 = n % 3

theorem mod_three_thm (n : Int) (h : Pre n) : mod_three_prop n := by
  unfold mod_three_prop
  unfold Pre at h
  induction h_eq : n.toNat using Nat.strong_induction_on generalizing n with
  | h k ih =>
    by_cases hn0 : n = 0
    · subst hn0; simp [mySumDigits_zero]
    · rw [mySumDigits_pos_step n (by omega)]
      have hrec : mySumDigits (n / 10) % 3 = (n / 10) % 3 :=
        ih (n / 10).toNat (by omega) (n / 10) (by omega) rfl
      omega

theorem mySumDigits_succ_le (n : Int) (hn : 0 ≤ n) :
    mySumDigits (n + 1) ≤ mySumDigits n + 1 := by
  induction h_eq : n.toNat using Nat.strong_induction_on generalizing n with
  | h k ih =>
    rw [mySumDigits_step (n + 1) (by omega), mySumDigits_step n hn]
    by_cases hmod : n % 10 < 9
    · have h1 : (n + 1) % 10 = n % 10 + 1 := by omega
      have h2 : (n + 1) / 10 = n / 10 := by omega
      rw [h1, h2]
      omega
    · have h1 : (n + 1) % 10 = 0 := by omega
      have h2 : (n + 1) / 10 = n / 10 + 1 := by omega
      have hrec : mySumDigits (n / 10 + 1) ≤ mySumDigits (n / 10) + 1 :=
        ih (n / 10).toNat (by omega) (n / 10) (by omega) rfl
      rw [h1, h2]
      omega

theorem mySumDigits_subadd (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    mySumDigits (a + b) ≤ mySumDigits a + mySumDigits b := by
  induction h_eq : (a + b).toNat using Nat.strong_induction_on generalizing a b with
  | h k ih =>
    by_cases hab : a + b = 0
    · have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      subst ha0; subst hb0
      simp [mySumDigits_zero]
    · rw [mySumDigits_step (a + b) (by omega), mySumDigits_step a ha, mySumDigits_step b hb]
      by_cases hcarry : a % 10 + b % 10 < 10
      · have hmod : (a + b) % 10 = a % 10 + b % 10 := by omega
        have hdiv : (a + b) / 10 = a / 10 + b / 10 := by omega
        have hrec : mySumDigits (a / 10 + b / 10) ≤ mySumDigits (a / 10) + mySumDigits (b / 10) :=
          ih (a / 10 + b / 10).toNat (by omega) (a / 10) (b / 10) (by omega) (by omega) rfl
        rw [hmod, hdiv]
        omega
      · have hmod : (a + b) % 10 = a % 10 + b % 10 - 10 := by omega
        have hdiv : (a + b) / 10 = a / 10 + b / 10 + 1 := by omega
        have hsucc : mySumDigits (a / 10 + b / 10 + 1) ≤ mySumDigits (a / 10 + b / 10) + 1 :=
          mySumDigits_succ_le (a / 10 + b / 10) (by omega)
        have hrec : mySumDigits (a / 10 + b / 10) ≤ mySumDigits (a / 10) + mySumDigits (b / 10) :=
          ih (a / 10 + b / 10).toNat (by omega) (a / 10) (b / 10) (by omega) (by omega) rfl
        rw [hmod, hdiv]
        omega

/-- Property 14: Subadditivity (`mySumDigits (n + m) <= mySumDigits n + mySumDigits m`). -/
def subadd_prop (n : Int) : Prop :=
  ∀ m : Int, Pre m → mySumDigits (n + m) ≤ mySumDigits n + mySumDigits m

theorem subadd_thm (n : Int) (h : Pre n) : subadd_prop n :=
  fun m hm => mySumDigits_subadd n m h hm

/-- Property 15: Agreement with Mathlib's `(Nat.digits 10 n.toNat).sum`. -/
def digits_sum_prop (n : Int) : Prop :=
  mySumDigits n = Int.ofNat ((Nat.digits 10 n.toNat).sum)

theorem digits_sum_thm (n : Int) (h : Pre n) : digits_sum_prop n := by
  unfold digits_sum_prop
  rw [mySumDigits_eq_sumDigitsNat n h, sumDigitsNat_eq_digits_sum]

theorem sumDigitsNat_digits_len_bound (k : Nat) :
    sumDigitsNat k ≤ 9 * (Nat.digits 10 k).length := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk0 : k = 0
    · subst hk0; simp [sumDigitsNat]
    · rw [sumDigitsNat_pos k (by omega)]
      rw [Nat.digits_def' (by decide : 1 < 10) (by omega : 0 < k)]
      simp only [List.length_cons]
      have hrec : sumDigitsNat (k / 10) ≤ 9 * (Nat.digits 10 (k / 10)).length :=
        ih (k / 10) (Nat.div_lt_self (by omega) (by decide))
      omega

/-- Property 16: Upper bound by `9` times the number of base-10 digits. -/
def digits_len_bound_prop (n : Int) : Prop :=
  mySumDigits n ≤ 9 * Int.ofNat (Nat.digits 10 n.toNat).length

theorem digits_len_bound_thm (n : Int) (h : Pre n) : digits_len_bound_prop n := by
  unfold digits_len_bound_prop
  rw [mySumDigits_eq_sumDigitsNat n h]
  have hnat := sumDigitsNat_digits_len_bound n.toNat
  simp only [Int.ofNat_eq_coe]
  omega

/-- Property 17: Checked wrapper returns `some (mySumDigits n)` iff `Pre n`,
    and `none` iff `not Pre n`. -/
def pre_check_prop (n : Int) : Prop :=
  (Pre n ↔ mySumDigitsOpt n = some (mySumDigits n)) ∧
  (¬ Pre n ↔ mySumDigitsOpt n = none)

theorem pre_check_thm (n : Int) : pre_check_prop n := by
  unfold pre_check_prop mySumDigitsOpt Pre
  by_cases h : n < 0
  · simp [h]
  · simp [h]
    omega

/-! ## 5. Post-condition -/

/-- Postcondition combining all specification properties of `mySumDigits`. -/
def Post_prop (n : Int) : Prop :=
  nonneg_prop n ∧
  single_digit_prop n ∧
  pos_prop n ∧
  zero_prop n ∧
  recurrence_prop n ∧
  upper_bound_prop n ∧
  strict_lt_prop n ∧
  fixed_point_prop n ∧
  lower_bound_prop n ∧
  append_digit_prop n ∧
  mul_ten_prop n ∧
  mod_nine_prop n ∧
  mod_three_prop n ∧
  subadd_prop n ∧
  digits_sum_prop n ∧
  digits_len_bound_prop n ∧
  pre_check_prop n

/-! ## 6. Property-Based Tests (PBTs) -/

-- Randomized PBTs via Plausible
#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n → 0 ≤ mySumDigits n)
#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n → n < 10 → mySumDigits n = n)
#eval Plausible.Testable.check (∀ n : Int, 0 < n → 0 < mySumDigits n)
#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n → (mySumDigits n = 0 ↔ n = 0))
#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n → mySumDigits n = n % 10 + mySumDigits (n / 10))
#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n → mySumDigits n ≤ n)
#eval Plausible.Testable.check (∀ n : Int, 10 ≤ n → mySumDigits n < n)
#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n → (mySumDigits n = n ↔ n < 10))
#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n → n % 10 ≤ mySumDigits n)
#eval Plausible.Testable.check (∀ n d : Int, 0 ≤ n → 0 ≤ d → d < 10 → mySumDigits (10 * n + d) = mySumDigits n + d)
#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n → mySumDigits (10 * n) = mySumDigits n)
#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n → mySumDigits n % 9 = n % 9)
#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n → mySumDigits n % 3 = n % 3)
#eval Plausible.Testable.check (∀ n m : Int, 0 ≤ n → 0 ≤ m → mySumDigits (n + m) ≤ mySumDigits n + mySumDigits m)
#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n → mySumDigits n = Int.ofNat ((Nat.digits 10 n.toNat).sum))
#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n → mySumDigits n ≤ 9 * Int.ofNat (Nat.digits 10 n.toNat).length)
#eval Plausible.Testable.check (∀ n : Int, (0 ≤ n ↔ mySumDigitsOpt n = some (mySumDigits n)) ∧ (n < 0 ↔ mySumDigitsOpt n = none))

-- Executable boolean checker for the full Post_prop on concrete inputs
def checkPostBool (n : Int) : Bool :=
  let s := mySumDigits n
  (0 ≤ s) &&
  (if n < 10 then s == n else true) &&
  (if 0 < n then 0 < s else true) &&
  ((s == 0) == (n == 0)) &&
  (s == n % 10 + mySumDigits (n / 10)) &&
  (s ≤ n) &&
  (if 10 ≤ n then s < n else true) &&
  ((s == n) == (n < 10)) &&
  (n % 10 ≤ s) &&
  ((List.range 10).all (fun d => mySumDigits (10 * n + Int.ofNat d) == s + Int.ofNat d)) &&
  (mySumDigits (10 * n) == s) &&
  (s % 9 == n % 9) &&
  (s % 3 == n % 3) &&
  ((List.range 20).all (fun m => mySumDigits (n + Int.ofNat m) ≤ s + mySumDigits (Int.ofNat m))) &&
  (s == Int.ofNat ((Nat.digits 10 n.toNat).sum)) &&
  (s ≤ 9 * Int.ofNat (Nat.digits 10 n.toNat).length) &&
  (mySumDigitsOpt n == some s)

#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n → checkPostBool n = true)

-- Bounded exhaustive PBTs covering every property over concrete ranges
example : (List.range 300).all (fun k => 0 ≤ mySumDigits (Int.ofNat k)) = true := by native_decide
example : (List.range 10).all (fun k => mySumDigits (Int.ofNat k) == Int.ofNat k) = true := by native_decide
example : (List.range 300).all (fun k => 0 < mySumDigits (Int.ofNat (k + 1))) = true := by native_decide
example : (List.range 300).all (fun k => (mySumDigits (Int.ofNat k) == 0) == (k == 0)) = true := by native_decide
example : (List.range 300).all (fun k =>
  let n := Int.ofNat k
  mySumDigits n == n % 10 + mySumDigits (n / 10)) = true := by native_decide
example : (List.range 300).all (fun k =>
  let n := Int.ofNat k
  mySumDigits n ≤ n) = true := by native_decide
example : (List.range 300).all (fun k =>
  let n := Int.ofNat (k + 10)
  mySumDigits n < n) = true := by native_decide
example : (List.range 300).all (fun k =>
  let n := Int.ofNat k
  (mySumDigits n == n) == (n < 10)) = true := by native_decide
example : (List.range 300).all (fun k =>
  let n := Int.ofNat k
  n % 10 ≤ mySumDigits n) = true := by native_decide
example : (List.range 100).all (fun k =>
  let n := Int.ofNat k
  (List.range 10).all (fun d =>
    mySumDigits (10 * n + Int.ofNat d) == mySumDigits n + Int.ofNat d)) = true := by native_decide
example : (List.range 300).all (fun k =>
  let n := Int.ofNat k
  mySumDigits (10 * n) == mySumDigits n) = true := by native_decide
example : (List.range 300).all (fun k =>
  let n := Int.ofNat k
  mySumDigits n % 9 == n % 9 && mySumDigits n % 3 == n % 3) = true := by native_decide
example : (List.range 50).all (fun k =>
  let n := Int.ofNat k
  (List.range 50).all (fun m =>
    let m' := Int.ofNat m
    mySumDigits (n + m') ≤ mySumDigits n + mySumDigits m')) = true := by native_decide
example : (List.range 300).all (fun k =>
  let n := Int.ofNat k
  mySumDigits n == Int.ofNat ((Nat.digits 10 k).sum)) = true := by native_decide
example : (List.range 300).all (fun k =>
  let n := Int.ofNat k
  mySumDigits n ≤ 9 * Int.ofNat (Nat.digits 10 k).length) = true := by native_decide
example : (List.range 300).all (fun k => checkPostBool (Int.ofNat k)) = true := by native_decide
example : (List.range 100).all (fun k => mySumDigitsOpt (- Int.ofNat (k + 1)) == none) = true := by native_decide

/-! ## 7. Correctness Theorem (`Pre -> Post`) -/

/-- Main correctness theorem: for every integer `n` satisfying `Pre n`, `Post_prop n` holds. -/
theorem mySumDigits_correct (n : Int) (h : Pre n) : Post_prop n :=
  ⟨nonneg_thm n h,
   single_digit_thm n h,
   pos_thm n h,
   zero_thm n h,
   recurrence_thm n h,
   upper_bound_thm n h,
   strict_lt_thm n h,
   fixed_point_thm n h,
   lower_bound_thm n h,
   append_digit_thm n h,
   mul_ten_thm n h,
   mod_nine_thm n h,
   mod_three_thm n h,
   subadd_thm n h,
   digits_sum_thm n h,
   digits_len_bound_thm n h,
   pre_check_thm n⟩

/-- Alias for `Pre -> Post` correctness theorem. -/
theorem correctness_thm (n : Int) : Pre n → Post_prop n :=
  mySumDigits_correct n

/-! ## 8. Imperative Implementation (`Id.run do`) -/

/-- Imperative implementation on `Nat` using `Id.run do` and mutable variables. -/
def sumDigitsNatImp (n : Nat) : Nat := Id.run do
  let mut m : Nat := n
  let mut total : Nat := 0
  for _ in List.range n do
    if m > 0 then
      total := total + m % 10
      m := m / 10
    else
      break
  return total

/-- Imperative implementation on `Int` using `Id.run do` and mutable variables
    mirroring the Python loop `while n > 0: total += n % 10; n //= 10`. -/
def mySumDigitsImp (n : Int) : Int := Id.run do
  let mut m : Int := n
  let mut total : Int := 0
  for _ in List.range n.toNat do
    if m > 0 then
      total := total + m % 10
      m := m / 10
    else
      break
  return total

/-- Checked imperative implementation returning `none` if `not pre n`. -/
def mySumDigitsOptImp (n : Int) : Option Int := Id.run do
  if n < 0 then
    return none
  let mut m : Int := n
  let mut total : Int := 0
  for _ in List.range n.toNat do
    if m > 0 then
      total := total + m % 10
      m := m / 10
    else
      break
  return some total

/-! ## 9. Imperative Tests -/

example : mySumDigitsImp 123 = 6 := by native_decide
example : mySumDigitsImp 0 = 0 := by native_decide
example : mySumDigitsImp 1 = 1 := by native_decide
example : mySumDigitsImp 9 = 9 := by native_decide
example : mySumDigitsImp 10 = 1 := by native_decide
example : mySumDigitsImp 999 = 27 := by native_decide
example : mySumDigitsImp 12345 = 15 := by native_decide
example : mySumDigitsImp (-1) = 0 := by native_decide

example : mySumDigitsOptImp 123 = some 6 := by native_decide
example : mySumDigitsOptImp 0 = some 0 := by native_decide
example : mySumDigitsOptImp (-1) = none := by native_decide

example : sumDigitsNatImp 123 = 6 := by native_decide
example : sumDigitsNatImp 0 = 0 := by native_decide
example : sumDigitsNatImp 9 = 9 := by native_decide

#eval mySumDigitsImp 123
#eval mySumDigitsImp 0
#eval mySumDigitsOptImp (-1)
#eval mySumDigitsOptImp 123

-- PBT comparing functional and imperative implementations
#eval Plausible.Testable.check (∀ n : Int, mySumDigits n = mySumDigitsImp n)
#eval Plausible.Testable.check (∀ n : Int, mySumDigitsOpt n = mySumDigitsOptImp n)
#eval Plausible.Testable.check (∀ n : Nat, sumDigitsNat n = sumDigitsNatImp n)
example : (List.range 300).all (fun k =>
  mySumDigits (Int.ofNat k) == mySumDigitsImp (Int.ofNat k)) = true := by native_decide

/-! ## 10. Equivalence Theorem: Functional = Imperative -/

private def natLoopStep (_ : Nat) (r : MProd Nat Nat) : Id (ForInStep (MProd Nat Nat)) :=
  if r.fst > 0 then
    do
      pure PUnit.unit
      pure (ForInStep.yield ⟨r.fst / 10, r.snd + r.fst % 10⟩)
  else
    pure (ForInStep.done ⟨r.fst, r.snd⟩)

private theorem nat_loop_eq (xs : List Nat) (m total : Nat) (h : m ≤ xs.length) :
    (forIn xs (⟨m, total⟩ : MProd Nat Nat) natLoopStep).run.snd = total + sumDigitsNat m := by
  induction xs generalizing m total with
  | nil =>
    have hm : m = 0 := Nat.eq_zero_of_le_zero h
    subst hm
    simp [sumDigitsNat]
  | cons _ xs ih =>
    simp only [List.forIn_cons, natLoopStep]
    by_cases hm : m > 0
    · simp only [hm, ↓reduceIte, bind, pure, Id.run]
      have hdiv : m / 10 ≤ xs.length := by
        simp only [List.length_cons] at h
        omega
      have ih_step := ih (m / 10) (total + m % 10) hdiv
      simp only [Id.run] at ih_step
      rw [ih_step]
      conv_rhs => rw [sumDigitsNat]
      have hm0 : ¬ (m = 0) := by omega
      simp only [hm0, ↓reduceIte]
      omega
    · have hm0 : m = 0 := by omega
      subst hm0
      simp [sumDigitsNat, bind, pure, Id.run]

/-- Equivalence theorem for the `Nat` implementations. -/
theorem sumDigitsNat_equiv (n : Nat) : sumDigitsNat n = sumDigitsNatImp n := by
  have hlen : n ≤ (List.range n).length := by simp
  have hloop := nat_loop_eq (List.range n) n 0 hlen
  unfold sumDigitsNatImp
  change sumDigitsNat n = (forIn (List.range n) (⟨n, 0⟩ : MProd Nat Nat) natLoopStep).run.snd
  omega

private def intLoopStep (_ : Nat) (r : MProd Int Int) : Id (ForInStep (MProd Int Int)) :=
  if r.fst > 0 then
    do
      pure PUnit.unit
      pure (ForInStep.yield ⟨r.fst / 10, r.snd + r.fst % 10⟩)
  else
    pure (ForInStep.done ⟨r.fst, r.snd⟩)

private theorem int_loop_eq (xs : List Nat) (m total : Int) (h : m.toNat ≤ xs.length) :
    (forIn xs (⟨m, total⟩ : MProd Int Int) intLoopStep).run.snd = total + mySumDigits m := by
  induction xs generalizing m total with
  | nil =>
    have hm0 : m ≤ 0 := by
      simp only [List.length_nil] at h
      omega
    rw [mySumDigits]
    simp [hm0]
  | cons _ xs ih =>
    simp only [List.forIn_cons, intLoopStep]
    by_cases hm : m > 0
    · simp only [hm, ↓reduceIte, bind, pure, Id.run]
      have hdiv_len : (m / 10).toNat ≤ xs.length := by
        simp only [List.length_cons] at h
        omega
      have ih_step := ih (m / 10) (total + m % 10) hdiv_len
      simp only [Id.run] at ih_step
      rw [ih_step]
      conv_rhs => rw [mySumDigits]
      have hnotle : ¬ (m ≤ 0) := by omega
      simp only [hnotle, ↓reduceIte]
      omega
    · have hm0 : m ≤ 0 := by omega
      conv_rhs => rw [mySumDigits]
      simp [hm, hm0, bind, pure, Id.run]

/-- Equivalence theorem: functional `mySumDigits` equals imperative `mySumDigitsImp` for all `n : Int`. -/
theorem mySumDigits_equiv (n : Int) : mySumDigits n = mySumDigitsImp n := by
  have hlen : n.toNat ≤ (List.range n.toNat).length := by simp
  have hloop := int_loop_eq (List.range n.toNat) n 0 hlen
  unfold mySumDigitsImp
  change mySumDigits n = (forIn (List.range n.toNat) (⟨n, 0⟩ : MProd Int Int) intLoopStep).run.snd
  omega

/-- Equivalence theorem under precondition `Pre n`. -/
theorem mySumDigits_equiv_under_pre (n : Int) (_h : Pre n) : mySumDigits n = mySumDigitsImp n :=
  mySumDigits_equiv n

/-- Equivalence theorem for the checked `Option Int` implementations. -/
theorem mySumDigitsOpt_equiv (n : Int) : mySumDigitsOpt n = mySumDigitsOptImp n := by
  unfold mySumDigitsOpt mySumDigitsOptImp
  by_cases hlt : n < 0
  · simp [hlt, pure, Id.run]
  · simp only [hlt, ↓reduceIte, bind, pure, Id.run]
    congr 1
    exact mySumDigits_equiv n

end MySumDigits
