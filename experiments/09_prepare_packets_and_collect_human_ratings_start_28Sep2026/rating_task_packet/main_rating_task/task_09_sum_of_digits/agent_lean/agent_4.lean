import Mathlib
import Plausible

/-!
# Sum of Digits

Lean 4 formalization of a Python program that returns the sum of decimal digits of a
non-negative integer.

Python reference:
- `pre(n)` holds iff `n` is a non-negative integer (`isinstance(n, int) and n >= 0`).
- `prog(n)` returns the sum of digits of `n`, computed by `total += n % 10; n //= 10`
  while `n > 0` (the sum of digits of `0` is `0`).
- If the precondition fails (negative integer, or a non-integer such as a float),
  `prog` raises `ValueError`.

The numeric content is formalized on `Nat`. Exceptional inputs are represented by
`PyVal`, so the `ValueError` cases in the Python tests (negative `int` and `float`)
are part of the specification rather than being erased by the type checker.
-/

namespace MySumDigits

/-- Python values that the reference tests feed to `prog`. -/
inductive PyVal where
  | int : Int → PyVal
  | float : Float → PyVal

/-- Error message, matching the Python `ValueError` text shape. -/
def errorMsg : PyVal → String
  | .int n => s!"Require non-negative integer (got n={n})"
  | .float x => s!"Require non-negative integer (got n={x})"

/-- Sum of decimal digits of a natural number.

This is the direct recursive reading of the Python loop
`while n > 0: total += n % 10; n //= 10`, with the explicit `n == 0` base case. -/
def sumDigits (n : Nat) : Nat :=
  if h : n = 0 then 0
  else n % 10 + sumDigits (n / 10)
termination_by n
decreasing_by
  simp_wf
  omega

/-- Functional implementation of the Python program, including precondition failures. -/
def prog (v : PyVal) : Except String Nat :=
  match v with
  | .int n =>
      if 0 ≤ n then
        .ok (sumDigits n.toNat)
      else
        .error (errorMsg (.int n))
  | .float x =>
      .error (errorMsg (.float x))

instance : BEq (Except String Nat) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

instance : DecidableEq (Except String Nat) := fun a b =>
  match a, b with
  | .ok x, .ok y =>
      if h : x = y then isTrue (by subst h; rfl)
      else isFalse (by intro hEq; cases hEq; exact h rfl)
  | .error x, .error y =>
      if h : x = y then isTrue (by subst h; rfl)
      else isFalse (by intro hEq; cases hEq; exact h rfl)
  | .ok _, .error _ => isFalse (by intro hEq; cases hEq)
  | .error _, .ok _ => isFalse (by intro hEq; cases hEq)

/-! ## Basic equations -/

theorem sumDigits_zero : sumDigits 0 = 0 := by
  unfold sumDigits
  simp

theorem sumDigits_of_pos (n : Nat) (h : 0 < n) :
    sumDigits n = n % 10 + sumDigits (n / 10) := by
  conv_lhs => unfold sumDigits
  simp only [dif_neg (Nat.ne_of_gt h)]

theorem sumDigits_eq_mod_add (n : Nat) :
    sumDigits n = n % 10 + sumDigits (n / 10) := by
  by_cases h : n = 0
  · subst h
    simp [sumDigits_zero]
  · exact sumDigits_of_pos n (Nat.pos_of_ne_zero h)

theorem sumDigits_lt_ten (n : Nat) (h : n < 10) : sumDigits n = n := by
  by_cases hz : n = 0
  · simp [hz, sumDigits_zero]
  · rw [sumDigits_of_pos n (Nat.pos_of_ne_zero hz)]
    have hd : n / 10 = 0 := Nat.div_eq_of_lt h
    simp [hd, sumDigits_zero, Nat.mod_eq_of_lt h]

/-- `sumDigits` is the sum of base-10 digits. -/
theorem sumDigits_eq_digits_sum (n : Nat) :
    sumDigits n = (Nat.digits 10 n).sum := by
  refine Nat.strongRecOn n ?_
  intro n ih
  cases n with
  | zero =>
    simp [sumDigits_zero, Nat.digits_zero]
  | succ n =>
    have hpos : 0 < n.succ := Nat.succ_pos n
    rw [sumDigits_of_pos _ hpos, Nat.digits_def' (by decide : 1 < 10) hpos, List.sum_cons]
    have hlt : n.succ / 10 < n.succ := Nat.div_lt_self hpos (by decide)
    exact congrArg (fun x => n.succ % 10 + x) (ih _ hlt)

/-- The recursive equation and the zero base case characterize `sumDigits`. -/
theorem sumDigits_unique (f : Nat → Nat)
    (h0 : f 0 = 0)
    (hstep : ∀ n, 0 < n → f n = n % 10 + f (n / 10)) :
    ∀ n, f n = sumDigits n := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih
  cases n with
  | zero => simp [h0, sumDigits_zero]
  | succ n =>
    have hpos : 0 < n.succ := Nat.succ_pos n
    rw [hstep _ hpos, sumDigits_of_pos _ hpos]
    have hlt : n.succ / 10 < n.succ := Nat.div_lt_self hpos (by decide)
    rw [ih _ hlt]

theorem sumDigits_modEq (n : Nat) : n ≡ sumDigits n [MOD 9] := by
  simpa [sumDigits_eq_digits_sum] using Nat.modEq_nine_digits_sum n

theorem sumDigits_le (n : Nat) : sumDigits n ≤ n := by
  simpa [sumDigits_eq_digits_sum] using Nat.digit_sum_le 10 n

theorem sumDigits_nine_dvd_iff (n : Nat) : 9 ∣ n ↔ 9 ∣ sumDigits n := by
  simpa [sumDigits_eq_digits_sum] using Nat.nine_dvd_iff n

/-! ## Unit tests -/

example : prog (.int 123) = .ok 6 := by native_decide
example : prog (.int 0) = .ok 0 := by native_decide
example : prog (.int 5) = .ok 5 := by native_decide
example : prog (.int 10) = .ok 1 := by native_decide
example : prog (.int 999) = .ok 27 := by native_decide
example : sumDigits 123 = 6 := by native_decide
example : sumDigits 0 = 0 := by native_decide

#eval prog (.int 123)
#eval prog (.int 0)
#eval sumDigits 2024

/-- Python `check` harness, including the negative and non-integer cases. -/
def check : Bool :=
  prog (.int 123) == .ok 6 &&
  prog (.int 0) == .ok 0 &&
  (match prog (.int (-1)) with | .error _ => true | .ok _ => false) &&
  (match prog (.float 3.14) with | .error _ => true | .ok _ => false)

example : check = true := by native_decide

/-! ## Pre-condition -/

/-- Python `pre`: the value is a non-negative integer. -/
def pre (v : PyVal) : Bool :=
  match v with
  | .int n => 0 ≤ n
  | .float _ => false

/-- Pre-condition predicate: input is a non-negative integer. -/
def Pre (v : PyVal) : Prop :=
  match v with
  | .int n => 0 ≤ n
  | .float _ => False

theorem pre_iff_Pre (v : PyVal) : pre v = true ↔ Pre v := by
  cases v with
  | int n =>
    simp [pre, Pre]
  | float x =>
    simp [pre, Pre]

/-! ## Properties -/

/-- Sum of digits of `0` is `0`. -/
def zero_prop : Prop := sumDigits 0 = 0

theorem zero_thm : zero_prop := sumDigits_zero

/-- A single-digit number is returned unchanged. -/
def single_digit_prop (n : Nat) : Prop := n < 10 → sumDigits n = n

theorem single_digit_thm (n : Nat) : single_digit_prop n :=
  fun h => sumDigits_lt_ten n h

/-- One step of the Python loop: peel off the least significant digit. -/
def recursion_prop (n : Nat) : Prop :=
  sumDigits n = n % 10 + sumDigits (n / 10)

theorem recursion_thm (n : Nat) : recursion_prop n :=
  sumDigits_eq_mod_add n

/-- Classic congruence: a number is congruent to the sum of its decimal digits modulo 9. -/
def mod9_prop (n : Nat) : Prop := n ≡ sumDigits n [MOD 9]

theorem mod9_thm (n : Nat) : mod9_prop n := sumDigits_modEq n

/-- The digit sum never exceeds the number itself. -/
def le_prop (n : Nat) : Prop := sumDigits n ≤ n

theorem le_thm (n : Nat) : le_prop n := sumDigits_le n

/-- The implementation agrees with Mathlib's base-10 digit expansion. -/
def digits_sum_prop (n : Nat) : Prop := sumDigits n = (Nat.digits 10 n).sum

theorem digits_sum_thm (n : Nat) : digits_sum_prop n := sumDigits_eq_digits_sum n

/-- Divisibility by 9 depends only on the digit sum. -/
def nine_dvd_prop (n : Nat) : Prop := 9 ∣ n ↔ 9 ∣ sumDigits n

theorem nine_dvd_thm (n : Nat) : nine_dvd_prop n := sumDigits_nine_dvd_iff n

/-- The recursive specification determines the function. -/
def unique_prop : Prop :=
  ∀ f : Nat → Nat,
    f 0 = 0 → (∀ n, 0 < n → f n = n % 10 + f (n / 10)) → ∀ n, f n = sumDigits n

theorem unique_thm : unique_prop := by
  intro f h0 hstep n
  exact sumDigits_unique f h0 hstep n

/-- Negative integers violate the precondition and produce an error (Python `ValueError`). -/
def neg_error_prop (n : Int) : Prop :=
  n < 0 → ∃ msg, prog (.int n) = .error msg

theorem neg_error_thm (n : Int) : neg_error_prop n := by
  intro hn
  have hnot : ¬ 0 ≤ n := not_le_of_gt hn
  refine ⟨errorMsg (.int n), ?_⟩
  simp [prog, hnot]

/-- Non-integers (floats) violate the precondition and produce an error. -/
def float_error_prop (x : Float) : Prop :=
  ∃ msg, prog (.float x) = .error msg

theorem float_error_thm (x : Float) : float_error_prop x := by
  refine ⟨errorMsg (.float x), ?_⟩
  simp [prog]

/-- On a non-negative integer the function returns the digit sum. -/
def nonneg_ok_prop (n : Int) : Prop :=
  0 ≤ n → prog (.int n) = .ok (sumDigits n.toNat)

theorem nonneg_ok_thm (n : Int) : nonneg_ok_prop n := by
  intro hn
  simp [prog, hn]

/-! ## Post-condition -/

/-- Post-condition of `prog`.

On a non-negative integer the result is `ok` of the digit sum, and that digit sum
satisfies the algorithm's recursive equation, the base-10 digit expansion, the
mod-9 congruence, the upper bound, and the single-digit equation.
On a negative integer or a float the result is an error, matching Python's `ValueError`.
-/
def Post_prop (v : PyVal) (r : Except String Nat) : Prop :=
  match v with
  | .int n =>
      if 0 ≤ n then
        r = .ok (sumDigits n.toNat) ∧
        digits_sum_prop n.toNat ∧
        mod9_prop n.toNat ∧
        le_prop n.toNat ∧
        single_digit_prop n.toNat ∧
        recursion_prop n.toNat ∧
        (n.toNat = 0 → zero_prop)
      else
        ∃ msg, r = .error msg
  | .float _ =>
      ∃ msg, r = .error msg

/-! ## Property-based tests -/

-- zero_prop
example : (sumDigits 0 == 0) = true := by native_decide
#eval Plausible.Testable.check (sumDigits 0 = 0)

-- single_digit_prop (bounded: random samples rarely satisfy n < 10)
example : (List.range 10).all (fun n => sumDigits n == n) = true := by native_decide
example : (List.range 30).all (fun n => !(n < 10) || sumDigits n == n) = true := by native_decide

-- recursion_prop
example : (List.range 80).all (fun n => sumDigits n == n % 10 + sumDigits (n / 10)) = true := by
  native_decide
#eval Plausible.Testable.check (∀ n : Nat, sumDigits n = n % 10 + sumDigits (n / 10))

-- mod9_prop, executable form of `n ≡ sumDigits n [MOD 9]`
example : (List.range 80).all (fun n => sumDigits n % 9 == n % 9) = true := by native_decide
#eval Plausible.Testable.check (∀ n : Nat, sumDigits n % 9 = n % 9)

-- le_prop
example : (List.range 80).all (fun n => sumDigits n ≤ n) = true := by native_decide
#eval Plausible.Testable.check (∀ n : Nat, sumDigits n ≤ n)

-- digits_sum_prop
example : (List.range 80).all (fun n => sumDigits n == (Nat.digits 10 n).sum) = true := by
  native_decide
#eval Plausible.Testable.check (∀ n : Nat, sumDigits n = (Nat.digits 10 n).sum)

-- nine_dvd_prop
example : (List.range 80).all (fun n => decide (9 ∣ n) == decide (9 ∣ sumDigits n)) = true := by
  native_decide
#eval Plausible.Testable.check (∀ n : Nat, 9 ∣ n ↔ 9 ∣ sumDigits n)

-- unique_prop quantifies over all functions `Nat → Nat`, which has no executable sampler.
-- PBT: not executable (quantifies over functions Nat → Nat)

-- neg_error_prop
example : (List.range 30).all (fun k =>
    match prog (.int (-(Int.ofNat (k + 1)))) with
    | .error _ => true
    | .ok _ => false) = true := by native_decide

-- float_error_prop: every float is rejected; the Python test uses `3.14`.
example : (match prog (.float 3.14) with | .error _ => true | .ok _ => false) = true := by
  native_decide
-- PBT: not executable as a random Float law (Float arithmetic is opaque).
-- The property is proved for every Float in `float_error_thm`.

-- nonneg_ok_prop
example : (List.range 40).all (fun n => prog (.int (Int.ofNat n)) == .ok (sumDigits n)) = true := by
  native_decide
#eval Plausible.Testable.check (∀ n : Nat, prog (.int (Int.ofNat n)) = .ok (sumDigits n))

/-- Executable form of `Post_prop` on non-negative integers. -/
def postBool (n : Nat) : Bool :=
  let r := sumDigits n
  prog (.int (Int.ofNat n)) == .ok r &&
    r == (Nat.digits 10 n).sum &&
    r % 9 == n % 9 &&
    r ≤ n &&
    (!(n < 10) || r == n) &&
    r == n % 10 + sumDigits (n / 10)

example : (List.range 60).all postBool = true := by native_decide
#eval Plausible.Testable.check (∀ n : Nat, postBool n = true)

example : (match prog (.int (-1)) with | .error _ => true | .ok _ => false) = true := by
  native_decide
example : (match prog (.float 3.14) with | .error _ => true | .ok _ => false) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (v : PyVal) (hpre : Pre v) : Post_prop v (prog v) := by
  cases v with
  | float _ =>
    simp [Pre] at hpre
  | int n =>
    dsimp [Pre] at hpre
    have hprog : prog (.int n) = .ok (sumDigits n.toNat) := by
      unfold prog
      simp [hpre]
    simp only [Post_prop]
    rw [if_pos hpre, hprog]
    refine ⟨rfl, sumDigits_eq_digits_sum n.toNat, sumDigits_modEq n.toNat,
      sumDigits_le n.toNat, sumDigits_lt_ten n.toNat, sumDigits_eq_mod_add n.toNat, ?_⟩
    intro _
    exact sumDigits_zero

/-- Full specification, including inputs that violate `Pre`. -/
theorem prog_spec (v : PyVal) : Post_prop v (prog v) := by
  cases v with
  | float x =>
    simp only [Post_prop, prog]
    exact ⟨errorMsg (.float x), rfl⟩
  | int n =>
    by_cases h : 0 ≤ n
    · exact correctness_thm (.int n) (by simpa [Pre] using h)
    · simp only [Post_prop, prog, if_neg h]
      exact ⟨errorMsg (.int n), rfl⟩

/-! ## Imperative implementation -/

/-- One iteration of `total, m = total + m % 10, m / 10` on the monomorphic pair
used by `Id` mutable state. -/
def mstep (p : MProd Nat Nat) : MProd Nat Nat :=
  ⟨p.fst / 10, p.snd + p.fst % 10⟩

/-- Same transition on an ordinary pair, used in the equivalence proof. -/
def step (p : Nat × Nat) : Nat × Nat :=
  (p.1 / 10, p.2 + p.1 % 10)

/-- Imperative digit sum.

`Id.run do` with mutable `total` and `m`, matching the Python loop
`total = 0; while n > 0: total += n % 10; n //= 10`.
The loop is a bounded `for` of `n + 1` iterations: each iteration divides by 10,
`n < 10^(n+1)`, and once `m = 0` further iterations add `0`, so the final `total`
is exactly the result of the `while` loop.
-/
def sumDigitsImp (n : Nat) : Nat :=
  Id.run do
    let mut total : Nat := 0
    let mut m : Nat := n
    for _ in List.range (n + 1) do
      total := total + m % 10
      m := m / 10
    return total

/-- Imperative implementation of `prog`, including the precondition check. -/
def progImp (v : PyVal) : Except String Nat :=
  match v with
  | .int n =>
      if 0 ≤ n then
        .ok (sumDigitsImp n.toNat)
      else
        .error (errorMsg (.int n))
  | .float x =>
      .error (errorMsg (.float x))

/-! ## Imperative tests -/

example : sumDigitsImp 123 = 6 := by native_decide
example : sumDigitsImp 0 = 0 := by native_decide
example : sumDigitsImp 999 = 27 := by native_decide
example : progImp (.int 123) = .ok 6 := by native_decide
example : progImp (.int 0) = .ok 0 := by native_decide
example : progImp (.int (-1)) = .error (errorMsg (.int (-1))) := by native_decide
example : (match progImp (.float 3.14) with | .error _ => true | .ok _ => false) = true := by
  native_decide

#eval sumDigitsImp 123
#eval progImp (.int 456)

example : (List.range 50).all (fun n => sumDigitsImp n == sumDigits n) = true := by native_decide

/-! ## Equivalence -/

theorem ten_pow_ge_self (k : Nat) : k ≤ 10 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hone : 1 ≤ 10 ^ k := Nat.one_le_pow k 10 (by decide)
    calc
      k + 1 ≤ 10 ^ k + 1 := Nat.add_le_add_right ih 1
      _ ≤ 10 ^ k + 10 ^ k := by omega
      _ = 2 * 10 ^ k := by omega
      _ ≤ 10 * 10 ^ k := by omega
      _ = 10 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

theorem nat_lt_ten_pow_succ (n : Nat) : n < 10 ^ (n + 1) := by
  have h : n + 1 ≤ 10 ^ (n + 1) := ten_pow_ge_self (n + 1)
  omega

/-- After `k` digit steps, with `m < 10^k`, the accumulator holds `total + sumDigits m`. -/
theorem iterate_spec (k m total : Nat) (hk : m < 10 ^ k) :
    (step^[k]) (m, total) = (m / 10 ^ k, total + sumDigits m) := by
  induction k generalizing m total with
  | zero =>
    have hm : m = 0 := by
      simpa [Nat.pow_zero] using hk
    simp [hm, sumDigits_zero, Function.iterate_zero]
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    have hm : m / 10 < 10 ^ k := by
      have hmul : m < 10 * 10 ^ k := by
        have hk' : m < 10 ^ k * 10 := by simpa [Nat.pow_succ] using hk
        rwa [Nat.mul_comm] at hk'
      exact Nat.div_lt_of_lt_mul hmul
    simp only [step]
    rw [ih (m / 10) (total + m % 10) hm]
    apply Prod.ext
    · simp [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
    · rw [sumDigits_eq_mod_add m, Nat.add_assoc]

theorem sumDigitsImp_eq_mfoldl (n : Nat) :
    sumDigitsImp n =
      (List.foldl (fun b (_ : Nat) => mstep b) ⟨n, 0⟩ (List.range (n + 1))).snd := by
  simp [sumDigitsImp, mstep]

def toProd (p : MProd Nat Nat) : Nat × Nat := (p.fst, p.snd)

theorem toProd_mstep (p : MProd Nat Nat) : toProd (mstep p) = step (toProd p) := by
  simp [toProd, mstep, step]

theorem mfoldl_toProd (k m total : Nat) :
    toProd (List.foldl (fun b (_ : Nat) => mstep b) ⟨m, total⟩ (List.range k))
      = (step^[k]) (m, total) := by
  induction k generalizing m total with
  | zero => simp [Function.iterate_zero, toProd]
  | succ k ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [toProd_mstep, ih]
    exact (Function.iterate_succ_apply' step k (m, total)).symm

/-- The imperative loop computes the same digit sum as the functional program. -/
theorem sumDigitsImp_eq (n : Nat) : sumDigitsImp n = sumDigits n := by
  rw [sumDigitsImp_eq_mfoldl]
  have h := mfoldl_toProd (n + 1) n 0
  have h2 := iterate_spec (n + 1) n 0 (nat_lt_ten_pow_succ n)
  have hsnd :
      (List.foldl (fun b (_ : Nat) => mstep b) ⟨n, 0⟩ (List.range (n + 1))).snd
        = ((step^[n + 1]) (n, 0)).2 := by
    have := congrArg Prod.snd h
    simpa [toProd] using this
  rw [hsnd, h2]
  simp

/-- Functional and imperative implementations agree on every Python input. -/
theorem equivalence_thm (v : PyVal) : prog v = progImp v := by
  cases v with
  | int n =>
    by_cases h : 0 ≤ n
    · simp [prog, progImp, h, sumDigitsImp_eq]
    · simp [prog, progImp, h]
  | float x =>
    simp [prog, progImp]

end MySumDigits
