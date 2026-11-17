import Mathlib

/-!
# 20_MySumDigits: Sum of Digits in a Non-Negative Integer

This module formalizes the Python program that computes the sum of base-10 digits
of a non-negative integer `n`.

## Structure
1. Functional implementation (`sumDigits`, `sumDigits?`)
2. Unit tests (`example` with `native_decide` and `#eval`)
3. Pre-condition predicate (`Pre`)
4. Property propositions (`<name>_prop`) and kernel-checked theorems (`<name>_thm`)
5. Post-condition predicate (`Post_prop`)
6. Property-based tests (Plausible randomized checks and bounded `native_decide` checks)
7. Correctness theorem (`Pre → Post_prop`)
8. Imperative implementation using `Id.run do` with mutable state (`sumDigitsImp`, `sumDigitsImp?`)
9. Imperative unit tests
10. Equivalence theorems (`sumDigits n = sumDigitsImp n` and `sumDigits? n = sumDigitsImp? n`)
-/

namespace «20_MySumDigits»

/-! ## Implementation (Functional Definition) -/

/-- Functional implementation returning the sum of base-10 digits of an integer `n`.
For `n ≤ 0`, it returns `0`; for `n > 0`, it recursively adds `n % 10` to `sumDigits (n / 10)`. -/
def sumDigits (n : Int) : Int :=
  if n ≤ 0 then 0
  else n % 10 + sumDigits (n / 10)
termination_by n.toNat

abbrev mySumDigits : Int → Int := sumDigits
abbrev prog : Int → Int := sumDigits

/-- Executable boolean precondition check corresponding to Python's `pre(n)`. -/
def preCheck (n : Int) : Bool :=
  decide (n ≥ 0)

/-- Checked functional implementation modeling Python's `ValueError` on negative inputs
by returning `none` when `n < 0` and `some (sumDigits n)` when `n ≥ 0`. -/
def sumDigits? (n : Int) : Option Int :=
  if n ≥ 0 then some (sumDigits n) else none

abbrev prog? : Int → Option Int := sumDigits?

/-! ## Unit Tests -/

example : sumDigits 123 = 6 := by native_decide
example : sumDigits 0 = 0 := by native_decide
example : sumDigits 1 = 1 := by native_decide
example : sumDigits 7 = 7 := by native_decide
example : sumDigits 9 = 9 := by native_decide
example : sumDigits 10 = 1 := by native_decide
example : sumDigits 99 = 18 := by native_decide
example : sumDigits 999 = 27 := by native_decide
example : sumDigits 10005 = 6 := by native_decide
example : sumDigits (-1) = 0 := by native_decide

example : sumDigits? 123 = some 6 := by native_decide
example : sumDigits? 0 = some 0 := by native_decide
example : sumDigits? 7 = some 7 := by native_decide
example : sumDigits? (-1) = none := by native_decide
example : sumDigits? (-42) = none := by native_decide

#eval sumDigits 123
#eval sumDigits 0
#eval sumDigits 7
#eval sumDigits 999
#eval sumDigits? 123
#eval sumDigits? 0
#eval sumDigits? (-1)

/-! ## Pre-Condition Predicate -/

/-- Pre-condition: `n` is a non-negative integer (`n ≥ 0`). -/
def Pre (n : Int) : Prop :=
  n ≥ 0

instance (n : Int) : Decidable (Pre n) :=
  inferInstanceAs (Decidable (n ≥ 0))

/-! ## Helper Lemmas for Functional Implementation -/

theorem sumDigits_le_zero {n : Int} (h : n ≤ 0) : sumDigits n = 0 := by
  unfold sumDigits
  simp [h]

theorem sumDigits_zero : sumDigits 0 = 0 :=
  sumDigits_le_zero (le_refl 0)

theorem sumDigits_pos_step {n : Int} (h : 0 < n) :
    sumDigits n = n % 10 + sumDigits (n / 10) := by
  conv_lhs => unfold sumDigits
  have h1 : ¬ (n ≤ 0) := by omega
  simp [h1]

theorem sumDigits_nonneg_all (n : Int) : 0 ≤ sumDigits n := by
  induction n using sumDigits.induct with
  | case1 n hn =>
    simp [sumDigits_le_zero hn]
  | case2 n hn ih =>
    have hpos : 0 < n := by omega
    rw [sumDigits_pos_step hpos]
    omega

theorem sumDigits_pos_of_pos {n : Int} (h : 0 < n) : 0 < sumDigits n := by
  induction n using sumDigits.induct with
  | case1 n hn => omega
  | case2 n hn ih =>
    have hpos : 0 < n := by omega
    rw [sumDigits_pos_step hpos]
    by_cases hdiv : 0 < n / 10
    · have := ih hdiv
      omega
    · have : n % 10 > 0 := by omega
      have := sumDigits_nonneg_all (n / 10)
      omega

theorem sumDigits_single_digit_aux {n : Int} (h0 : 0 ≤ n) (h10 : n < 10) :
    sumDigits n = n := by
  by_cases hz : n ≤ 0
  · have : n = 0 := by omega
    subst this
    exact sumDigits_zero
  · have hpos : 0 < n := by omega
    rw [sumDigits_pos_step hpos]
    have hdiv : n / 10 ≤ 0 := by omega
    rw [sumDigits_le_zero hdiv]
    omega

/-! ## Property Propositions and Theorems -/

/-- Property 1: The sum of digits is always non-negative (`sumDigits n ≥ 0`). -/
def nonneg_prop (n : Int) : Prop :=
  sumDigits n ≥ 0

instance (n : Int) : Decidable (nonneg_prop n) :=
  inferInstanceAs (Decidable (sumDigits n ≥ 0))

theorem nonneg_thm (n : Int) (_h : Pre n) : nonneg_prop n :=
  sumDigits_nonneg_all n

/-- Property 2: Edge case for `0` — the sum of digits of `0` is `0`. -/
def zero_prop (n : Int) : Prop :=
  n = 0 → sumDigits n = 0

instance (n : Int) : Decidable (zero_prop n) :=
  inferInstanceAs (Decidable (n = 0 → sumDigits n = 0))

theorem zero_thm (n : Int) (_h : Pre n) : zero_prop n := by
  intro hn
  subst hn
  exact sumDigits_zero

/-- Property 3: For non-negative `n`, `sumDigits n = 0` if and only if `n = 0`. -/
def zero_iff_prop (n : Int) : Prop :=
  sumDigits n = 0 ↔ n = 0

instance (n : Int) : Decidable (zero_iff_prop n) :=
  inferInstanceAs (Decidable (sumDigits n = 0 ↔ n = 0))

theorem zero_iff_thm (n : Int) (h : Pre n) : zero_iff_prop n := by
  unfold zero_iff_prop
  unfold Pre at h
  constructor
  · intro hsum
    by_contra hne
    have hpos : 0 < n := by omega
    have hsum_pos := sumDigits_pos_of_pos hpos
    omega
  · intro hn
    subst hn
    exact sumDigits_zero

/-- Property 4: For strictly positive `n`, the sum of digits is strictly positive (`sumDigits n > 0`). -/
def pos_prop (n : Int) : Prop :=
  n > 0 → sumDigits n > 0

instance (n : Int) : Decidable (pos_prop n) :=
  inferInstanceAs (Decidable (n > 0 → sumDigits n > 0))

theorem pos_thm (n : Int) (_h : Pre n) : pos_prop n := by
  intro hpos
  exact sumDigits_pos_of_pos hpos

/-- Property 5: Single-digit non-negative numbers (`0 ≤ n < 10`) return themselves. -/
def single_digit_prop (n : Int) : Prop :=
  (0 ≤ n ∧ n < 10) → sumDigits n = n

instance (n : Int) : Decidable (single_digit_prop n) :=
  inferInstanceAs (Decidable ((0 ≤ n ∧ n < 10) → sumDigits n = n))

theorem single_digit_thm (n : Int) (_h : Pre n) : single_digit_prop n := by
  intro ⟨h0, h10⟩
  exact sumDigits_single_digit_aux h0 h10

/-- Property 6: Recurrence step for positive integers (`n > 0 → sumDigits n = n % 10 + sumDigits (n / 10)`). -/
def recurrence_prop (n : Int) : Prop :=
  n > 0 → sumDigits n = n % 10 + sumDigits (n / 10)

instance (n : Int) : Decidable (recurrence_prop n) :=
  inferInstanceAs (Decidable (n > 0 → sumDigits n = n % 10 + sumDigits (n / 10)))

theorem recurrence_thm (n : Int) (_h : Pre n) : recurrence_prop n := by
  intro hpos
  exact sumDigits_pos_step hpos

/-- Property 7: Base-10 digit decomposition holds for all non-negative integers `n`. -/
def decomp_prop (n : Int) : Prop :=
  sumDigits n = n % 10 + sumDigits (n / 10)

instance (n : Int) : Decidable (decomp_prop n) :=
  inferInstanceAs (Decidable (sumDigits n = n % 10 + sumDigits (n / 10)))

theorem decomp_thm (n : Int) (h : Pre n) : decomp_prop n := by
  unfold decomp_prop
  unfold Pre at h
  by_cases hz : n = 0
  · subst hz
    simp [sumDigits_zero]
  · have hpos : 0 < n := by omega
    exact sumDigits_pos_step hpos

/-- Property 8: The sum of digits of a non-negative integer never exceeds the integer itself (`sumDigits n ≤ n`). -/
def le_self_prop (n : Int) : Prop :=
  sumDigits n ≤ n

instance (n : Int) : Decidable (le_self_prop n) :=
  inferInstanceAs (Decidable (sumDigits n ≤ n))

theorem le_self_thm (n : Int) (h : Pre n) : le_self_prop n := by
  unfold le_self_prop
  unfold Pre at h
  induction n using sumDigits.induct with
  | case1 n hn =>
    rw [sumDigits_le_zero hn]
    omega
  | case2 n hn ih =>
    have hpos : 0 < n := by omega
    rw [sumDigits_pos_step hpos]
    have hdiv_nonneg : 0 ≤ n / 10 := by omega
    have ih_step := ih hdiv_nonneg
    omega

/-- Property 9: For multi-digit integers (`n ≥ 10`), the sum of digits is strictly less than `n`. -/
def lt_self_prop (n : Int) : Prop :=
  n ≥ 10 → sumDigits n < n

instance (n : Int) : Decidable (lt_self_prop n) :=
  inferInstanceAs (Decidable (n ≥ 10 → sumDigits n < n))

theorem lt_self_thm (n : Int) (_h : Pre n) : lt_self_prop n := by
  intro h10
  have hpos : 0 < n := by omega
  rw [sumDigits_pos_step hpos]
  have hdiv_nonneg : Pre (n / 10) := by
    unfold Pre
    omega
  have hle : sumDigits (n / 10) ≤ n / 10 := le_self_thm (n / 10) hdiv_nonneg
  omega

/-- Property 10: Congruence modulo 9 (casting out nines: `sumDigits n % 9 = n % 9`). -/
def mod_nine_prop (n : Int) : Prop :=
  sumDigits n % 9 = n % 9

instance (n : Int) : Decidable (mod_nine_prop n) :=
  inferInstanceAs (Decidable (sumDigits n % 9 = n % 9))

theorem mod_nine_thm (n : Int) (h : Pre n) : mod_nine_prop n := by
  unfold mod_nine_prop
  unfold Pre at h
  induction n using sumDigits.induct with
  | case1 n hn =>
    have : n = 0 := by omega
    subst this
    simp [sumDigits_zero]
  | case2 n hn ih =>
    have hpos : 0 < n := by omega
    rw [sumDigits_pos_step hpos]
    have hdiv_nonneg : 0 ≤ n / 10 := by omega
    have ih_step := ih hdiv_nonneg
    omega

/-- Property 11: Appending a base-10 digit `d` (`0 ≤ d < 10`) adds `d` to the digit sum. -/
def append_digit_prop (n d : Int) : Prop :=
  (0 ≤ d ∧ d < 10) → sumDigits (10 * n + d) = sumDigits n + d

instance (n d : Int) : Decidable (append_digit_prop n d) :=
  inferInstanceAs (Decidable ((0 ≤ d ∧ d < 10) → sumDigits (10 * n + d) = sumDigits n + d))

theorem append_digit_thm (n d : Int) (h : Pre n) : append_digit_prop n d := by
  unfold append_digit_prop
  unfold Pre at h
  intro ⟨hd0, hd10⟩
  by_cases h0 : 10 * n + d ≤ 0
  · have hn0 : n = 0 := by omega
    have hd_zero : d = 0 := by omega
    subst hn0 hd_zero
    simp [sumDigits_zero]
  · have hpos : 0 < 10 * n + d := by omega
    rw [sumDigits_pos_step hpos]
    have hdiv : (10 * n + d) / 10 = n := by omega
    have hmod : (10 * n + d) % 10 = d := by omega
    rw [hdiv, hmod]
    omega

/-- Property 12: Multiplying a non-negative integer by 10 preserves the sum of digits. -/
def scale_ten_prop (n : Int) : Prop :=
  sumDigits (10 * n) = sumDigits n

instance (n : Int) : Decidable (scale_ten_prop n) :=
  inferInstanceAs (Decidable (sumDigits (10 * n) = sumDigits n))

theorem scale_ten_thm (n : Int) (h : Pre n) : scale_ten_prop n := by
  unfold scale_ten_prop
  have happ := append_digit_thm n 0 h ⟨le_refl 0, by decide⟩
  simpa using happ

/-- Property 13: Incrementing a non-negative integer by 1 increases the digit sum by at most 1. -/
def succ_bound_prop (n : Int) : Prop :=
  sumDigits (n + 1) ≤ sumDigits n + 1

instance (n : Int) : Decidable (succ_bound_prop n) :=
  inferInstanceAs (Decidable (sumDigits (n + 1) ≤ sumDigits n + 1))

theorem succ_bound_thm (n : Int) (h : Pre n) : succ_bound_prop n := by
  unfold succ_bound_prop
  unfold Pre at h
  induction n using sumDigits.induct with
  | case1 n hn0 =>
    have : n = 0 := by omega
    subst this
    have h1 : sumDigits 1 = 1 := sumDigits_single_digit_aux (by omega) (by omega)
    simp only [zero_add, h1, sumDigits_zero]
    omega
  | case2 n hn0 ih =>
    have hpos : 0 < n := by omega
    have hpos1 : 0 < n + 1 := by omega
    rw [sumDigits_pos_step hpos, sumDigits_pos_step hpos1]
    by_cases h9 : n % 10 < 9
    · have hdiv : (n + 1) / 10 = n / 10 := by omega
      have hmod : (n + 1) % 10 = n % 10 + 1 := by omega
      rw [hdiv, hmod]
      omega
    · have hdiv : (n + 1) / 10 = n / 10 + 1 := by omega
      have hmod : (n + 1) % 10 = 0 := by omega
      have hmodn : n % 10 = 9 := by omega
      rw [hdiv, hmod]
      have ih_step := ih (by omega)
      omega

/-- Property 14: Subadditivity — `sumDigits (a + b) ≤ sumDigits a + sumDigits b` for non-negative `a, b`. -/
def subadd_prop (a b : Int) : Prop :=
  sumDigits (a + b) ≤ sumDigits a + sumDigits b

instance (a b : Int) : Decidable (subadd_prop a b) :=
  inferInstanceAs (Decidable (sumDigits (a + b) ≤ sumDigits a + sumDigits b))

theorem subadd_thm (a b : Int) (ha : Pre a) (hb : Pre b) : subadd_prop a b := by
  unfold subadd_prop
  unfold Pre at ha hb
  induction a using sumDigits.induct generalizing b with
  | case1 a ha0 =>
    have : a = 0 := by omega
    subst this
    simp [sumDigits_zero]
  | case2 a ha0 ih =>
    have hapos : 0 < a := by omega
    by_cases hb0 : b ≤ 0
    · have : b = 0 := by omega
      subst this
      simp [sumDigits_zero]
    · have hbpos : 0 < b := by omega
      have habpos : 0 < a + b := by omega
      rw [sumDigits_pos_step hapos, sumDigits_pos_step hbpos, sumDigits_pos_step habpos]
      by_cases hcarry : a % 10 + b % 10 < 10
      · have hdiv : (a + b) / 10 = a / 10 + b / 10 := by omega
        have hmod : (a + b) % 10 = a % 10 + b % 10 := by omega
        rw [hdiv, hmod]
        have ih1 := ih (by omega) (b := b / 10) (by omega)
        omega
      · have hdiv : (a + b) / 10 = a / 10 + (b / 10 + 1) := by omega
        have hmod : (a + b) % 10 = a % 10 + b % 10 - 10 := by omega
        rw [hdiv, hmod]
        have ih1 := ih (by omega) (b := b / 10 + 1) (by omega)
        have hsucc : sumDigits (b / 10 + 1) ≤ sumDigits (b / 10) + 1 :=
          succ_bound_thm (b / 10) (by unfold Pre; omega)
        omega

/-- Property 15: Exact correspondence with Mathlib's `Nat.digits 10`. -/
def digits_sum_prop (n : Int) : Prop :=
  sumDigits n = ((Nat.digits 10 n.toNat).sum : Int)

instance (n : Int) : Decidable (digits_sum_prop n) :=
  inferInstanceAs (Decidable (sumDigits n = ((Nat.digits 10 n.toNat).sum : Int)))

theorem digits_sum_thm (n : Int) (_h : Pre n) : digits_sum_prop n := by
  clear _h
  unfold digits_sum_prop
  induction n using sumDigits.induct with
  | case1 n hn =>
    have htoNat : n.toNat = 0 := by omega
    simp [sumDigits_le_zero hn, htoNat]
  | case2 n hn ih =>
    have hpos : 0 < n := by omega
    rw [sumDigits_pos_step hpos, ih]
    have htoNat_pos : 0 < n.toNat := by omega
    rw [Nat.digits_def' (by decide : 1 < 10) htoNat_pos]
    simp only [List.sum_cons, Nat.cast_add]
    have hmod : ((n.toNat % 10 : Nat) : Int) = n % 10 := by omega
    have hdiv : n.toNat / 10 = (n / 10).toNat := by omega
    rw [hmod, hdiv]

/-- Property 16: On valid inputs (`Pre n`), `sumDigits? n` returns `some (sumDigits n)`. -/
def checked_valid_prop (n : Int) : Prop :=
  sumDigits? n = some (sumDigits n)

instance (n : Int) : Decidable (checked_valid_prop n) :=
  inferInstanceAs (Decidable (sumDigits? n = some (sumDigits n)))

theorem checked_valid_thm (n : Int) (h : Pre n) : checked_valid_prop n := by
  unfold checked_valid_prop sumDigits?
  unfold Pre at h
  simp [h]

/-- Property 17: On negative inputs (`n < 0`), `sumDigits? n` returns `none` (modeling `ValueError`). -/
def checked_neg_prop (n : Int) : Prop :=
  n < 0 → sumDigits? n = none

instance (n : Int) : Decidable (checked_neg_prop n) :=
  inferInstanceAs (Decidable (n < 0 → sumDigits? n = none))

theorem checked_neg_thm (n : Int) : checked_neg_prop n := by
  unfold checked_neg_prop sumDigits?
  intro hneg
  have hnot : ¬ (n ≥ 0) := by omega
  simp [hnot]

/-! ## Post-Condition -/

/-- Post-condition conjunction of properties for a valid input `n`. -/
def Post_prop (n : Int) : Prop :=
  nonneg_prop n ∧
  zero_prop n ∧
  zero_iff_prop n ∧
  pos_prop n ∧
  single_digit_prop n ∧
  recurrence_prop n ∧
  decomp_prop n ∧
  le_self_prop n ∧
  lt_self_prop n ∧
  mod_nine_prop n ∧
  scale_ten_prop n ∧
  succ_bound_prop n ∧
  digits_sum_prop n ∧
  checked_valid_prop n

instance (n : Int) : Decidable (Post_prop n) :=
  inferInstanceAs (Decidable (
    nonneg_prop n ∧
    zero_prop n ∧
    zero_iff_prop n ∧
    pos_prop n ∧
    single_digit_prop n ∧
    recurrence_prop n ∧
    decomp_prop n ∧
    le_self_prop n ∧
    lt_self_prop n ∧
    mod_nine_prop n ∧
    scale_ten_prop n ∧
    succ_bound_prop n ∧
    digits_sum_prop n ∧
    checked_valid_prop n))

/-! ## Property-Based Tests -/

-- Randomized PBTs with Plausible
#eval Plausible.Testable.check (∀ n : Int, Pre n → nonneg_prop n) { numRetries := 20 }
#eval Plausible.Testable.check (∀ n : Int, Pre n → zero_prop n) { numRetries := 20 }
#eval Plausible.Testable.check (∀ n : Int, Pre n → zero_iff_prop n) { numRetries := 20 }
#eval Plausible.Testable.check (∀ n : Int, Pre n → pos_prop n) { numRetries := 20 }
#eval Plausible.Testable.check (∀ n : Int, Pre n → single_digit_prop n) { numRetries := 20 }
#eval Plausible.Testable.check (∀ n : Int, Pre n → recurrence_prop n) { numRetries := 20 }
#eval Plausible.Testable.check (∀ n : Int, Pre n → decomp_prop n) { numRetries := 20 }
#eval Plausible.Testable.check (∀ n : Int, Pre n → le_self_prop n) { numRetries := 20 }
#eval Plausible.Testable.check (∀ n : Int, Pre n → lt_self_prop n) { numRetries := 20 }
#eval Plausible.Testable.check (∀ n : Int, Pre n → mod_nine_prop n) { numRetries := 20 }
#eval Plausible.Testable.check (∀ (n d : Int), Pre n → append_digit_prop n d) { numRetries := 20 }
#eval Plausible.Testable.check (∀ n : Int, Pre n → scale_ten_prop n) { numRetries := 20 }
#eval Plausible.Testable.check (∀ n : Int, Pre n → succ_bound_prop n) { numRetries := 20 }
#eval Plausible.Testable.check (∀ a b : Int, Pre a → Pre b → subadd_prop a b) { numRetries := 20 }
#eval Plausible.Testable.check (∀ n : Int, Pre n → digits_sum_prop n) { numRetries := 20 }
#eval Plausible.Testable.check (∀ n : Int, Pre n → checked_valid_prop n) { numRetries := 20 }
#eval Plausible.Testable.check (∀ n : Int, checked_neg_prop n) { numRetries := 20 }
#eval Plausible.Testable.check (∀ n : Int, Pre n → Post_prop n) { numRetries := 20 }

-- Bounded exhaustive PBTs over executable Boolean forms
example : (List.range 250).all (fun k => sumDigits (k : Int) ≥ 0) = true := by native_decide
example : (List.range 250).all (fun k => !(k == 0) || sumDigits (k : Int) == 0) = true := by native_decide
example : (List.range 250).all (fun k => (sumDigits (k : Int) == 0) == (k == 0)) = true := by native_decide
example : (List.range 250).all (fun k => !(k > 0) || sumDigits (k : Int) > 0) = true := by native_decide
example : (List.range 250).all (fun k => !(k < 10) || sumDigits (k : Int) == (k : Int)) = true := by native_decide
example : (List.range 250).all (fun k =>
    !(k > 0) || sumDigits (k : Int) == (k : Int) % 10 + sumDigits ((k : Int) / 10)) = true := by native_decide
example : (List.range 250).all (fun k =>
    sumDigits (k : Int) == (k : Int) % 10 + sumDigits ((k : Int) / 10)) = true := by native_decide
example : (List.range 250).all (fun k => sumDigits (k : Int) ≤ (k : Int)) = true := by native_decide
example : (List.range 250).all (fun k => !(k ≥ 10) || sumDigits (k : Int) < (k : Int)) = true := by native_decide
example : (List.range 250).all (fun k => sumDigits (k : Int) % 9 == (k : Int) % 9) = true := by native_decide
example : (List.range 50).all (fun k =>
    (List.range 10).all (fun d =>
      sumDigits (10 * (k : Int) + (d : Int)) == sumDigits (k : Int) + (d : Int))) = true := by native_decide
example : (List.range 250).all (fun k => sumDigits (10 * (k : Int)) == sumDigits (k : Int)) = true := by native_decide
example : (List.range 250).all (fun k => sumDigits ((k : Int) + 1) ≤ sumDigits (k : Int) + 1) = true := by native_decide
example : (List.range 40).all (fun a =>
    (List.range 40).all (fun b =>
      sumDigits ((a : Int) + (b : Int)) ≤ sumDigits (a : Int) + sumDigits (b : Int))) = true := by native_decide
example : (List.range 250).all (fun k =>
    sumDigits (k : Int) == ((Nat.digits 10 k).sum : Int)) = true := by native_decide
example : (List.range 250).all (fun k =>
    sumDigits? (k : Int) == some (sumDigits (k : Int))) = true := by native_decide
example : (List.range 100).all (fun k =>
    sumDigits? (-(k : Int) - 1) == none) = true := by native_decide
example : (List.range 250).all (fun k => decide (Post_prop (k : Int))) = true := by native_decide

/-! ## Correctness Theorem: `Pre -> Post` -/

/-- Main correctness theorem: every integer `n` satisfying `Pre n` satisfies `Post_prop n`. -/
theorem correctness_thm (n : Int) (h : Pre n) : Post_prop n :=
  ⟨nonneg_thm n h,
   zero_thm n h,
   zero_iff_thm n h,
   pos_thm n h,
   single_digit_thm n h,
   recurrence_thm n h,
   decomp_thm n h,
   le_self_thm n h,
   lt_self_thm n h,
   mod_nine_thm n h,
   scale_ten_thm n h,
   succ_bound_thm n h,
   digits_sum_thm n h,
   checked_valid_thm n h⟩

abbrev sumDigits_correct : ∀ n : Int, Pre n → Post_prop n := correctness_thm

/-! ## Imperative Implementation -/

/-- Imperative implementation of `sumDigits` using `Id.run do` and mutable state. -/
def sumDigitsImp (n : Int) : Int := Id.run do
  if n ≤ 0 then
    return 0
  let mut total : Int := 0
  let mut m : Int := n
  for _ in List.range n.toNat do
    if m > 0 then
      total := total + m % 10
      m := m / 10
  return total

abbrev mySumDigitsImp : Int → Int := sumDigitsImp
abbrev progImp : Int → Int := sumDigitsImp

/-- Checked imperative implementation returning `none` when `n < 0` and `some total` when `n ≥ 0`,
directly mirroring the structure of Python's `prog`. -/
def sumDigitsImp? (n : Int) : Option Int := Id.run do
  if ¬ (n ≥ 0) then
    return none
  if n == 0 then
    return some 0
  let mut total : Int := 0
  let mut m : Int := n
  for _ in List.range n.toNat do
    if m > 0 then
      total := total + m % 10
      m := m / 10
  return some total

/-! ## Imperative Tests -/

example : sumDigitsImp 123 = 6 := by native_decide
example : sumDigitsImp 0 = 0 := by native_decide
example : sumDigitsImp 1 = 1 := by native_decide
example : sumDigitsImp 7 = 7 := by native_decide
example : sumDigitsImp 9 = 9 := by native_decide
example : sumDigitsImp 10 = 1 := by native_decide
example : sumDigitsImp 99 = 18 := by native_decide
example : sumDigitsImp 999 = 27 := by native_decide
example : sumDigitsImp 10005 = 6 := by native_decide
example : sumDigitsImp (-1) = 0 := by native_decide

example : sumDigitsImp? 123 = some 6 := by native_decide
example : sumDigitsImp? 0 = some 0 := by native_decide
example : sumDigitsImp? (-1) = none := by native_decide

#eval sumDigitsImp 123
#eval sumDigitsImp 0
#eval sumDigitsImp 999
#eval sumDigitsImp? 123
#eval sumDigitsImp? (-1)

/-! ## Equivalence Theorem: Functional = Imperative -/

private theorem loop_invariant (xs : List Nat) (m total : Int) (hm : m.toNat ≤ xs.length) :
    (Id.run (forIn xs (⟨m, total⟩ : MProd Int Int) (fun _ r => do
      if r.fst > 0 then
        return ForInStep.yield ⟨r.fst / 10, r.snd + r.fst % 10⟩
      else
        return ForInStep.yield ⟨r.fst, r.snd⟩))).snd = total + sumDigits m := by
  induction xs generalizing m total with
  | nil =>
    simp only [List.length_nil, Nat.le_zero] at hm
    have hm0 : m ≤ 0 := by omega
    simp [sumDigits_le_zero hm0]
  | cons _ tl ih =>
    simp only [List.length_cons] at hm
    by_cases hpos : m > 0
    · simp only [List.forIn_cons, hpos, ↓reduceIte, pure_bind]
      have hdiv : (m / 10).toNat ≤ tl.length := by omega
      have ih_step := ih (m / 10) (total + m % 10) hdiv
      simp only [Id.run] at ih_step ⊢
      rw [ih_step, sumDigits_pos_step hpos]
      omega
    · simp only [List.forIn_cons, hpos, ↓reduceIte, pure_bind]
      have hdiv : m.toNat ≤ tl.length := by omega
      have ih_step := ih m total hdiv
      simp only [Id.run] at ih_step ⊢
      rw [ih_step]

/-- Equivalence theorem between the functional implementation `sumDigits`
and the imperative implementation `sumDigitsImp`. -/
theorem equivalence_thm (n : Int) : sumDigits n = sumDigitsImp n := by
  unfold sumDigitsImp
  by_cases hn : n ≤ 0
  · simp [hn, sumDigits_le_zero hn]
  · simp only [hn, ↓reduceIte]
    have hlen : n.toNat ≤ (List.range n.toNat).length := by simp
    have hinv := loop_invariant (List.range n.toNat) n 0 hlen
    simpa [Id.run] using hinv.symm

/-- Equivalence theorem under the precondition `Pre n`. -/
theorem equivalence_pre_thm (n : Int) (_h : Pre n) : sumDigits n = sumDigitsImp n :=
  equivalence_thm n

/-- Equivalence theorem for the checked implementations `sumDigits?` and `sumDigitsImp?`. -/
theorem checked_equivalence_thm (n : Int) : sumDigits? n = sumDigitsImp? n := by
  unfold sumDigits? sumDigitsImp?
  by_cases hneg : n ≥ 0
  · by_cases hz : n = 0
    · subst hz
      simp [sumDigits_zero]
    · have hnotle : ¬ (n ≤ 0) := by omega
      have hbeq : (n == 0) = false := beq_false_of_ne hz
      simp only [hneg, not_true_eq_false, ↓reduceIte, hbeq, Bool.false_eq_true]
      have hlen : n.toNat ≤ (List.range n.toNat).length := by simp
      have hinv := loop_invariant (List.range n.toNat) n 0 hlen
      simp only [Id.run, zero_add] at hinv
      exact congrArg some hinv.symm
  · simp [hneg]

#eval Plausible.Testable.check (∀ n : Int, sumDigits n = sumDigitsImp n)
example : (List.range 250).all (fun k => decide (sumDigits (k : Int) = sumDigitsImp (k : Int))) = true := by native_decide

end «20_MySumDigits»
