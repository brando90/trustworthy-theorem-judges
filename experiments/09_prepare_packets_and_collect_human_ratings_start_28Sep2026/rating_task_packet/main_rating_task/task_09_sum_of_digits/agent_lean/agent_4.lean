import Mathlib

/-!
# Sum of decimal digits

Lean translation of a Python program that returns the sum of the decimal digits
of a non-negative integer.

The Python function raises `ValueError` unless its argument is an `int` with
`n ≥ 0`. Negative integers and non-integers (the suite uses `3.14`) are
rejected. On a valid input the loop `total += n % 10; n //= 10` runs while
`n > 0`, and the sum of the digits of `0` is `0`.
-/

namespace «20_MySumDigits»

/-- Values that can be passed where Python accepts a dynamic object.

* `ofInt` is a Python `int`.
* `ofFloat` is a Python `float` (the tests pass `3.14`). Every float fails
  `isinstance(n, int)`, including integral values such as `2.0`.
* `ofNonInt` stands for every other non-`int` (strings, `None`, lists, …).
-/
inductive Input
  | ofInt (n : Int)
  | ofFloat (x : Float)
  | ofNonInt
  deriving Repr

/-- Message carried by the Lean counterpart of Python's `ValueError`. -/
def errMsg : String := "Require non-negative integer"

/-- Sum of decimal digits, by the same recurrence as the Python loop.

The `n = 0` branch is the loop that does not run. For `n > 0` one step adds
`n % 10` and continues on `n // 10`. -/
def sumDigits (n : Nat) : Nat :=
  if n = 0 then 0 else n % 10 + sumDigits (n / 10)
termination_by n

theorem sumDigits_zero : sumDigits 0 = 0 := by
  rw [sumDigits.eq_def]
  simp only [if_true]

theorem sumDigits_rec (n : Nat) : sumDigits n = n % 10 + sumDigits (n / 10) := by
  rw [sumDigits.eq_def]
  split_ifs with h
  · subst h
    rw [Nat.zero_div, sumDigits_zero, Nat.zero_mod]
  · rfl

instance instDecidableEqExcept {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α) := fun a b =>
  match a, b with
  | .error x, .error y =>
      if h : x = y then isTrue (congrArg Except.error h)
      else isFalse (fun heq => by cases heq; exact h rfl)
  | .ok x, .ok y =>
      if h : x = y then isTrue (congrArg Except.ok h)
      else isFalse (fun heq => by cases heq; exact h rfl)
  | .error _, .ok _ => isFalse (fun h => by cases h)
  | .ok _, .error _ => isFalse (fun h => by cases h)

/-- Functional translation of Python `prog`, including the precondition check. -/
def prog (x : Input) : Except String Nat :=
  match x with
  | .ofFloat _ => .error errMsg
  | .ofNonInt => .error errMsg
  | .ofInt n => if 0 ≤ n then .ok (sumDigits n.toNat) else .error errMsg

/-! ## Unit tests -/

example : prog (.ofInt 123) = .ok 6 := by native_decide

example : prog (.ofInt 0) = .ok 0 := by native_decide

example : prog (.ofInt 5) = .ok 5 := by native_decide

example : prog (.ofInt 10) = .ok 1 := by native_decide

example : prog (.ofInt 999) = .ok 27 := by native_decide

example : prog (.ofInt (-1)) = .error errMsg := by native_decide

example : prog (.ofFloat 3.14) = .error errMsg := by native_decide

example : prog (.ofFloat 2.0) = .error errMsg := by native_decide

example : prog .ofNonInt = .error errMsg := by native_decide

#eval prog (.ofInt 123)
#eval prog (.ofInt 0)
#eval prog (.ofInt 10)
#eval prog (.ofInt (-1))
#eval prog (.ofFloat 3.14)
#eval prog .ofNonInt

/-! ## Precondition -/

/-- Boolean form of Python `pre`: `isinstance(n, int) and n ≥ 0`. -/
def pre (x : Input) : Bool :=
  match x with
  | .ofInt n => decide (0 ≤ n)
  | .ofFloat _ => false
  | .ofNonInt => false

/-- `x` is a non-negative integer. -/
def Pre (x : Input) : Prop := pre x = true

theorem pre_ofInt_iff (n : Int) : Pre (.ofInt n) ↔ 0 ≤ n := by
  unfold Pre pre
  simp

theorem not_pre_float (x : Float) : ¬ Pre (.ofFloat x) := by
  simp [Pre, pre]

theorem not_pre_nonInt : ¬ Pre .ofNonInt := by
  simp [Pre, pre]

/-! ## Properties -/

abbrev zero_prop : Prop := sumDigits 0 = 0

theorem zero_thm : zero_prop := sumDigits_zero

abbrev single_digit_prop (n : Nat) : Prop := n < 10 → sumDigits n = n

theorem single_digit_thm (n : Nat) : single_digit_prop n := by
  intro hn
  rw [sumDigits_rec, Nat.div_eq_of_lt hn, Nat.mod_eq_of_lt hn, sumDigits_zero, Nat.add_zero]

abbrev recurrence_prop (n : Nat) : Prop := sumDigits n = n % 10 + sumDigits (n / 10)

theorem recurrence_thm (n : Nat) : recurrence_prop n := sumDigits_rec n

abbrev digits_sum_prop (n : Nat) : Prop := sumDigits n = (Nat.digits 10 n).sum

theorem digits_sum_thm (n : Nat) : digits_sum_prop n := by
  unfold digits_sum_prop
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      rw [sumDigits_zero, Nat.digits_zero, List.sum_nil]
    | succ n =>
      have hne : n + 1 ≠ 0 := Nat.succ_ne_zero n
      have hlt : (n + 1) / 10 < n + 1 := Nat.div_lt_self (Nat.succ_pos n) (by decide)
      rw [sumDigits_rec, Nat.digits_eq_cons_digits_div (by decide : 1 < 10) hne, List.sum_cons]
      exact congrArg (fun z => (n + 1) % 10 + z) (ih _ hlt)

/-- `sumDigits n ≡ n (mod 9)`, the usual digit-sum congruence. -/
abbrev mod_nine_prop (n : Nat) : Prop := sumDigits n ≡ n [MOD 9]

theorem mod_nine_thm (n : Nat) : mod_nine_prop n := by
  unfold mod_nine_prop
  rw [digits_sum_thm n]
  exact (Nat.modEq_nine_digits_sum n).symm

abbrev le_self_prop (n : Nat) : Prop := sumDigits n ≤ n

theorem le_self_thm (n : Nat) : le_self_prop n := by
  unfold le_self_prop
  rw [digits_sum_thm n]
  exact Nat.digit_sum_le 10 n

abbrev eq_zero_iff_prop (n : Nat) : Prop := sumDigits n = 0 ↔ n = 0

theorem eq_zero_iff_thm (n : Nat) : eq_zero_iff_prop n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    constructor
    · intro h
      cases n with
      | zero => rfl
      | succ n =>
        rw [sumDigits_rec] at h
        obtain ⟨hmod, hrest⟩ := Nat.add_eq_zero.mp h
        have hlt : (n + 1) / 10 < n + 1 := Nat.div_lt_self (Nat.succ_pos n) (by decide)
        have hdiv : (n + 1) / 10 = 0 := (ih _ hlt).mp hrest
        have hrepr : n + 1 = 10 * ((n + 1) / 10) + (n + 1) % 10 := (Nat.div_add_mod (n + 1) 10).symm
        omega
    · rintro rfl
      exact sumDigits_zero

/-- For `n ≥ 10` the digit sum is strictly smaller than `n`. -/
abbrev strict_lt_prop (n : Nat) : Prop := 10 ≤ n → sumDigits n < n

theorem strict_lt_thm (n : Nat) : strict_lt_prop n := by
  intro hn
  have hq : 0 < n / 10 := Nat.div_pos hn (by decide)
  rw [sumDigits_rec]
  have hle : sumDigits (n / 10) ≤ n / 10 := le_self_thm (n / 10)
  have hmul : 1 * (n / 10) < 10 * (n / 10) :=
    Nat.mul_lt_mul_of_pos_right (by decide : 1 < 10) hq
  have hstep : n / 10 + n % 10 < n := by
    have hrepr : n = 10 * (n / 10) + n % 10 := (Nat.div_add_mod n 10).symm
    have : n / 10 < 10 * (n / 10) := by simpa using hmul
    omega
  have : n % 10 + sumDigits (n / 10) ≤ n % 10 + n / 10 := Nat.add_le_add_left hle _
  omega

/-- The digit sum equals the number exactly on the single-digit inputs. -/
abbrev eq_self_iff_prop (n : Nat) : Prop := sumDigits n = n ↔ n < 10

theorem eq_self_iff_thm (n : Nat) : eq_self_iff_prop n := by
  constructor
  · intro h
    by_contra hge
    have hlt : sumDigits n < n := strict_lt_thm n (Nat.le_of_not_lt hge)
    omega
  · intro hn
    exact single_digit_thm n hn

/-- Each decimal digit is at most `9`, so the sum is at most nine times the length. -/
abbrev digit_bound_prop (n : Nat) : Prop := sumDigits n ≤ 9 * (Nat.digits 10 n).length

theorem list_sum_le_mul_length {l : List Nat} {c : Nat}
    (h : ∀ d ∈ l, d ≤ c) : l.sum ≤ c * l.length := by
  induction l with
  | nil => simp
  | cons d ds ih =>
    rw [List.sum_cons, List.length_cons]
    have hd : d ≤ c := h d List.mem_cons_self
    have hds : ds.sum ≤ c * ds.length := ih (fun x hx => h x (List.mem_cons_of_mem d hx))
    calc
      d + ds.sum ≤ c + c * ds.length := Nat.add_le_add hd hds
      _ = c * ds.length + c := Nat.add_comm _ _
      _ = c * (ds.length + 1) := by rw [← Nat.mul_succ]

theorem digit_bound_thm (n : Nat) : digit_bound_prop n := by
  unfold digit_bound_prop
  rw [digits_sum_thm n]
  refine list_sum_le_mul_length ?_
  intro d hd
  have : d < 10 := Nat.digits_lt_base (by decide : 1 < 10) hd
  omega

/-- Appending a zero digit does not change the digit sum: `sumDigits (n * 10) = sumDigits n`. -/
abbrev trailing_zero_prop (n : Nat) : Prop := sumDigits (n * 10) = sumDigits n

/-- Splitting off the lowest `k` digits: if `b < 10^k` then
`sumDigits (a * 10^k + b) = sumDigits a + sumDigits b`. -/
abbrev split_prop (k a b : Nat) : Prop :=
  b < 10 ^ k → sumDigits (a * 10 ^ k + b) = sumDigits a + sumDigits b

theorem split_thm (k a b : Nat) : split_prop k a b := by
  intro hb
  induction k generalizing a b with
  | zero =>
    have hb0 : b = 0 := by
      simpa [Nat.pow_zero, Nat.lt_one_iff] using hb
    subst hb0
    simp [sumDigits_zero]
  | succ k ih =>
    set q : Nat := b / 10
    set r : Nat := b % 10
    have hr : r < 10 := Nat.mod_lt b (by decide)
    have hb_repr : b = 10 * q + r := by
      simpa [q, r, Nat.mul_comm] using (Nat.div_add_mod b 10).symm
    have hq : q < 10 ^ k := by
      have hb' : b < 10 * 10 ^ k := by
        rw [Nat.pow_succ, Nat.mul_comm] at hb
        exact hb
      simpa [q] using Nat.div_lt_of_lt_mul hb'
    have hbody : a * 10 ^ (k + 1) + b = 10 * (a * 10 ^ k + q) + r := by
      calc
        a * 10 ^ (k + 1) + b
            = a * (10 ^ k * 10) + (10 * q + r) := by rw [Nat.pow_succ, hb_repr]
        _ = a * 10 ^ k * 10 + 10 * q + r := by ring
        _ = 10 * (a * 10 ^ k + q) + r := by ring
    have hdiv : (10 * (a * 10 ^ k + q) + r) / 10 = a * 10 ^ k + q := by
      rw [Nat.add_comm, Nat.add_mul_div_left r _ (by decide), Nat.div_eq_of_lt hr, Nat.zero_add]
    have hmod : (10 * (a * 10 ^ k + q) + r) % 10 = r := by
      rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hr]
    have hsumN : sumDigits (a * 10 ^ (k + 1) + b) = sumDigits (a * 10 ^ k + q) + r := by
      rw [hbody, sumDigits_rec, hdiv, hmod, Nat.add_comm]
    have hdivB : (10 * q + r) / 10 = q := by
      rw [Nat.add_comm, Nat.add_mul_div_left r _ (by decide), Nat.div_eq_of_lt hr, Nat.zero_add]
    have hmodB : (10 * q + r) % 10 = r := by
      rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hr]
    have hsumB : sumDigits b = sumDigits q + r := by
      rw [hb_repr, sumDigits_rec, hdivB, hmodB, Nat.add_comm]
    rw [hsumN, ih a q hq, hsumB, Nat.add_assoc]

theorem trailing_zero_thm (n : Nat) : trailing_zero_prop n := by
  have h := split_thm 1 n 0 (by decide : 0 < 10 ^ 1)
  simpa [trailing_zero_prop, Nat.pow_one, sumDigits_zero, Nat.add_zero] using h

abbrev neg_error_prop (n : Int) : Prop := n < 0 → prog (.ofInt n) = .error errMsg

theorem neg_error_thm (n : Int) : neg_error_prop n := by
  intro hn
  simp [prog, if_neg (not_le_of_gt hn)]

abbrev float_error_prop : Prop := ∀ x : Float, prog (.ofFloat x) = .error errMsg

theorem float_error_thm : float_error_prop := by
  intro _
  rfl

abbrev nonint_error_prop : Prop := prog .ofNonInt = .error errMsg

theorem nonint_error_thm : nonint_error_prop := rfl

abbrev ok_result_prop (n : Nat) : Prop := prog (.ofInt (n : Int)) = .ok (sumDigits n)

theorem ok_result_thm (n : Nat) : ok_result_prop n := by
  unfold ok_result_prop
  have hn : 0 ≤ (n : Int) := by omega
  simp [prog, hn, Int.toNat_natCast]

/-- Full input/output specification, including both `ValueError` cases. -/
abbrev result_spec_prop (x : Input) (r : Except String Nat) : Prop :=
  match x with
  | .ofFloat _ => r = .error errMsg
  | .ofNonInt => r = .error errMsg
  | .ofInt n =>
      if 0 ≤ n then r = .ok ((Nat.digits 10 n.toNat).sum) else r = .error errMsg

theorem result_spec_thm (x : Input) : result_spec_prop x (prog x) := by
  cases x with
  | ofFloat _ => simp [result_spec_prop, prog]
  | ofNonInt => simp [result_spec_prop, prog]
  | ofInt n =>
      by_cases hn : 0 ≤ n
      · simp only [result_spec_prop, prog, hn]
        exact congrArg Except.ok (digits_sum_thm n.toNat)
      · simp [result_spec_prop, prog, hn]

/-! ## Post-condition -/

/-- Post-condition of one call, packaged as the conjunction of the proved properties.

On the call itself, `result_spec_prop` requires the decimal digit sum when the
input is a non-negative integer and `ValueError` otherwise. The remaining
conjuncts are the algebraic properties of that digit sum.
-/
abbrev Post_prop (x : Input) (r : Except String Nat) : Prop :=
  result_spec_prop x r ∧
  zero_prop ∧
  (∀ n, single_digit_prop n) ∧
  (∀ n, recurrence_prop n) ∧
  (∀ n, digits_sum_prop n) ∧
  (∀ n, mod_nine_prop n) ∧
  (∀ n, le_self_prop n) ∧
  (∀ n, eq_zero_iff_prop n) ∧
  (∀ n, strict_lt_prop n) ∧
  (∀ n, eq_self_iff_prop n) ∧
  (∀ n, digit_bound_prop n) ∧
  (∀ n, trailing_zero_prop n) ∧
  (∀ k a b, split_prop k a b) ∧
  (∀ n, neg_error_prop n) ∧
  float_error_prop ∧
  nonint_error_prop ∧
  (∀ n, ok_result_prop n)

/-! ## Property-based tests

Executable checks of each stated property. A passing check is evidence, not a proof.
-/

#eval Plausible.Testable.check zero_prop

example : (List.range 10).all (fun n => sumDigits n == n) = true := by native_decide

#eval Plausible.Testable.check (∀ n : Nat, single_digit_prop n)

#eval Plausible.Testable.check (∀ n : Nat, recurrence_prop n)

#eval Plausible.Testable.check (∀ n : Nat, digits_sum_prop n)

#eval Plausible.Testable.check (∀ n : Nat, mod_nine_prop n)

#eval Plausible.Testable.check (∀ n : Nat, le_self_prop n)

#eval Plausible.Testable.check (∀ n : Nat, eq_zero_iff_prop n)

#eval Plausible.Testable.check (∀ n : Nat, strict_lt_prop n)

example : (List.range 40).all (fun n => decide (n < 10) || sumDigits n < n) = true := by
  native_decide

#eval Plausible.Testable.check (∀ n : Nat, eq_self_iff_prop n)

#eval Plausible.Testable.check (∀ n : Nat, digit_bound_prop n)

#eval Plausible.Testable.check (∀ n : Nat, trailing_zero_prop n)

-- Sparse guard `b < 10^k`: exhaustive small range, plus a random check.
example :
    ((List.range 4).all fun k =>
      (List.range 12).all fun a =>
        (List.range (min (10 ^ k) 30)).all fun b =>
          sumDigits (a * 10 ^ k + b) == sumDigits a + sumDigits b) = true := by
  native_decide

-- `b < 10^k` is sparse for independent samples, so the random check draws the low
-- part as `b % 10^k`, which is exactly the admissible range of `split_prop`.
#eval Plausible.Testable.check (∀ k a b : Nat,
  sumDigits (a * 10 ^ k + b % 10 ^ k) = sumDigits a + sumDigits (b % 10 ^ k))

example : (List.range 20).all (fun i =>
    prog (.ofInt (-(Int.ofNat i) - 1)) == .error errMsg) = true := by
  native_decide

#eval Plausible.Testable.check (∀ n : Int, neg_error_prop n)

-- `float_error_prop` is `∀ x : Float, …`. Float has no Plausible sampler here;
-- the property does not inspect the float, and these values include the Python
-- test `3.14` together with `2.0` (an integral float, still not an `int`).
example : ([3.14, -1.5, 0.0, 2.0, -0.0] : List Float).all
    (fun x => prog (.ofFloat x) == .error errMsg) = true := by native_decide

#eval Plausible.Testable.check nonint_error_prop

#eval Plausible.Testable.check (∀ n : Nat, ok_result_prop n)

-- `result_spec_prop` ranges over `Input`, which has no Plausible sampler.
-- This exhaustive slice covers the Python tests: `123`, `0`, `-1`, and `3.14`.
example : ([Input.ofNonInt, .ofFloat 3.14, .ofFloat 2.0, .ofFloat (-1.5),
    .ofInt (-5), .ofInt (-1), .ofInt 0, .ofInt 7, .ofInt 10, .ofInt 123, .ofInt 999].all
    (fun x => match x, prog x with
      | .ofFloat _, .error m => m == errMsg
      | .ofNonInt, .error m => m == errMsg
      | .ofInt n, .ok r => decide (0 ≤ n) && r == (Nat.digits 10 n.toNat).sum
      | .ofInt n, .error m => decide (n < 0) && m == errMsg
      | _, _ => false)) = true := by native_decide

-- Executable form of `Post_prop` on admissible inputs (non-negative integers).
example : (List.range 50).all (fun n =>
    let r := sumDigits n
    r == (Nat.digits 10 n).sum &&
    r % 9 == n % 9 &&
    decide (r ≤ n) &&
    ((r == 0) == (n == 0)) &&
    (decide (n < 10) || r < n) &&
    ((r == n) == decide (n < 10)) &&
    decide (r ≤ 9 * (Nat.digits 10 n).length) &&
    sumDigits (n * 10) == r &&
    r == n % 10 + sumDigits (n / 10)) = true := by native_decide

-- `Post_prop` also quantifies over `Float` (no Plausible sampler). The check below is
-- the executable Nat payload of the post-condition, including the successful call.
#eval Plausible.Testable.check (∀ n : Nat,
  sumDigits n = (Nat.digits 10 n).sum ∧
  sumDigits n % 9 = n % 9 ∧
  sumDigits n ≤ n ∧
  sumDigits n = n % 10 + sumDigits (n / 10) ∧
  sumDigits n ≤ 9 * (Nat.digits 10 n).length ∧
  sumDigits (n * 10) = sumDigits n ∧
  prog (.ofInt (n : Int)) = .ok (sumDigits n))

/-! ## Correctness: Pre → Post -/

theorem correctness_thm (x : Input) (hPre : Pre x) : Post_prop x (prog x) := by
  cases x with
  | ofFloat y => exact False.elim ((not_pre_float y) hPre)
  | ofNonInt => exact False.elim (not_pre_nonInt hPre)
  | ofInt n =>
      have _hn : 0 ≤ n := (pre_ofInt_iff n).mp hPre
      exact ⟨result_spec_thm (.ofInt n), zero_thm, single_digit_thm, recurrence_thm, digits_sum_thm,
        mod_nine_thm, le_self_thm, eq_zero_iff_thm, strict_lt_thm, eq_self_iff_thm, digit_bound_thm,
        trailing_zero_thm, split_thm, neg_error_thm, float_error_thm, nonint_error_thm,
        ok_result_thm⟩

/-! ## Imperative implementation

Python's `while n > 0` loop, written with mutable state in `Id`. The iteration
count is `n + 1`. That is enough to consume every digit (`n < 10^(n+1)`), and
once the remaining value is `0` each further step adds `0` and stays at `0`,
so the extra iterations match the loop guard `n > 0`.
-/

def sumDigitsImp (n : Nat) : Nat :=
  Id.run do
    let mut state : Nat × Nat := (n, 0)
    for _ in List.range (n + 1) do
      state := (state.1 / 10, state.2 + state.1 % 10)
    return state.2

def progImp (x : Input) : Except String Nat :=
  match x with
  | .ofFloat _ => .error errMsg
  | .ofNonInt => .error errMsg
  | .ofInt n => if 0 ≤ n then .ok (sumDigitsImp n.toNat) else .error errMsg

/-! ## Imperative tests -/

example : progImp (.ofInt 123) = .ok 6 := by native_decide

example : progImp (.ofInt 0) = .ok 0 := by native_decide

example : progImp (.ofInt 5) = .ok 5 := by native_decide

example : progImp (.ofInt 10) = .ok 1 := by native_decide

example : progImp (.ofInt 999) = .ok 27 := by native_decide

example : progImp (.ofInt (-1)) = .error errMsg := by native_decide

example : progImp (.ofFloat 3.14) = .error errMsg := by native_decide

example : progImp .ofNonInt = .error errMsg := by native_decide

example : sumDigitsImp 123 = sumDigits 123 := by native_decide

example : sumDigitsImp 0 = 0 := by native_decide

#eval progImp (.ofInt 123)
#eval progImp (.ofInt 0)
#eval progImp (.ofInt (-1))
#eval progImp (.ofFloat 3.14)
#eval sumDigitsImp 456

/-! ## Equivalence -/

/-- State of the imperative loop after `k` steps, starting from `(start, 0)`. -/
def foldSteps (k start : Nat) : Nat × Nat :=
  (List.range k).foldl (fun p (_ : Nat) => (p.1 / 10, p.2 + p.1 % 10)) (start, 0)

theorem foldSteps_zero (start : Nat) : foldSteps 0 start = (start, 0) := by
  simp [foldSteps]

theorem foldSteps_succ (k start : Nat) :
    foldSteps (k + 1) start =
      ((foldSteps k start).1 / 10, (foldSteps k start).2 + (foldSteps k start).1 % 10) := by
  unfold foldSteps
  rw [List.range_succ]
  simp [List.foldl_append]

theorem foldSteps_fst (k start : Nat) : (foldSteps k start).1 = start / 10 ^ k := by
  induction k generalizing start with
  | zero =>
    simp [foldSteps_zero, Nat.div_one]
  | succ k ih =>
    rw [foldSteps_succ, ih, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

theorem foldSteps_snd (k start : Nat) :
    (foldSteps k start).2 + sumDigits (start / 10 ^ k) = sumDigits start := by
  induction k generalizing start with
  | zero =>
    simp [foldSteps_zero, Nat.div_one]
  | succ k ih =>
    have hq : (foldSteps k start).1 = start / 10 ^ k := foldSteps_fst k start
    have hdiv : start / 10 ^ k / 10 = start / 10 ^ (k + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
    calc
      (foldSteps (k + 1) start).2 + sumDigits (start / 10 ^ (k + 1))
          = ((foldSteps k start).2 + (foldSteps k start).1 % 10) +
              sumDigits (start / 10 ^ (k + 1)) := by
            rw [foldSteps_succ]
      _ = (foldSteps k start).2 +
            ((start / 10 ^ k) % 10 + sumDigits (start / 10 ^ (k + 1))) := by
            rw [hq, Nat.add_assoc]
      _ = (foldSteps k start).2 + sumDigits (start / 10 ^ k) := by
            rw [← hdiv, ← sumDigits_rec]
      _ = sumDigits start := ih start

theorem nat_lt_ten_pow_succ (n : Nat) : n < 10 ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hone : 1 ≤ 10 ^ (n + 1) := Nat.one_le_pow (n + 1) 10 (by decide)
    have h1 : n + 1 < 10 ^ (n + 1) + 1 := Nat.add_lt_add_right ih 1
    have h2 : 10 ^ (n + 1) + 1 ≤ 10 ^ (n + 1) + 10 ^ (n + 1) :=
      Nat.add_le_add_left hone _
    have h3 : 10 ^ (n + 1) + 10 ^ (n + 1) = 2 * 10 ^ (n + 1) := by
      rw [Nat.two_mul]
    have h4 : 2 * 10 ^ (n + 1) ≤ 10 * 10 ^ (n + 1) :=
      Nat.mul_le_mul_right _ (by decide)
    have h5 : 10 * 10 ^ (n + 1) = 10 ^ (n + 2) := by
      rw [Nat.mul_comm, ← Nat.pow_succ]
    exact lt_of_lt_of_le h1 (le_trans h2 (le_trans (le_of_eq h3) (le_trans h4 (le_of_eq h5))))

theorem sumDigitsImp_eq_fold (n : Nat) : sumDigitsImp n = (foldSteps (n + 1) n).2 := by
  unfold sumDigitsImp foldSteps
  simp only [Id.run_bind, Id.run_pure, pure_bind]
  have hbody :
      (fun (_x : Nat) (r : Nat × Nat) =>
        pure (ForInStep.yield (r.1 / 10, r.2 + r.1 % 10))) =
      (fun (_x : Nat) (r : Nat × Nat) =>
        ForInStep.yield <$> (pure (r.1 / 10, r.2 + r.1 % 10) : Id (Nat × Nat))) := by
    funext _ r
    rfl
  rw [hbody]
  exact congrArg Prod.snd
    (List.idRun_forIn_yield_eq_foldl (List.range (n + 1))
      (fun (_x : Nat) (r : Nat × Nat) => pure (r.1 / 10, r.2 + r.1 % 10)) (n, 0))

theorem sumDigitsImp_eq_sumDigits (n : Nat) : sumDigitsImp n = sumDigits n := by
  rw [sumDigitsImp_eq_fold]
  have hdiv : n / 10 ^ (n + 1) = 0 := Nat.div_eq_of_lt (nat_lt_ten_pow_succ n)
  have hs := foldSteps_snd (n + 1) n
  rw [hdiv, sumDigits_zero, Nat.add_zero] at hs
  exact hs

abbrev equiv_prop (x : Input) : Prop := prog x = progImp x

theorem equiv_thm (x : Input) : equiv_prop x := by
  unfold equiv_prop
  cases x with
  | ofFloat _ => rfl
  | ofNonInt => rfl
  | ofInt n =>
      by_cases h : 0 ≤ n
      · simp [prog, progImp, h, sumDigitsImp_eq_sumDigits]
      · simp [prog, progImp, h]

-- PBT for the equivalence property.
example : (List.range 40).all (fun n => sumDigits n == sumDigitsImp n) = true := by native_decide

#eval Plausible.Testable.check (∀ n : Nat, sumDigits n = sumDigitsImp n)

example : (List.range 15).all (fun n =>
    prog (.ofInt (n : Int)) == progImp (.ofInt (n : Int)) &&
    prog (.ofInt (-(n : Int) - 1)) == progImp (.ofInt (-(n : Int) - 1))) = true := by
  native_decide

end «20_MySumDigits»
