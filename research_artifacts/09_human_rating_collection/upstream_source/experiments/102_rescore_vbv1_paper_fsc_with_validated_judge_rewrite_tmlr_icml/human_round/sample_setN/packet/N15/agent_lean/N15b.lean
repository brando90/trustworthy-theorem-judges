import Mathlib

/-!
# VeriBench Task 20 — Sum of Digits

Formalization of the Python program `prog`, which returns the sum of the
decimal digits of a non-negative integer and raises `ValueError` otherwise:

```python
def prog(n: int) -> int:
    if not pre(n):
        raise ValueError(...)
    if n == 0:
        return 0
    total = 0
    while n > 0:
        total += n % 10
        n //= 10
    return total
```

Contents:
* `mySumDigits` — functional implementation on `Nat`.
* `Pre` — the precondition (non-negative integer).
* Properties and proofs: value at `0`, single digits, digit append,
  `mySumDigits n ≤ n`, and casting out nines.
* `Post_prop` — postcondition as a conjunction of properties.
* `prog` — an `Except` model of the Python function including `ValueError`.
* `mySumDigitsImp` — imperative implementation in `Id` with mutable state,
  proved equal to the functional one.
-/

namespace MySumDigits20

/-! ## Functional implementation -/

/-- Sum of the decimal digits of a non-negative integer. -/
def mySumDigits (n : Nat) : Nat :=
  if h : n = 0 then 0
  else mySumDigits (n / 10) + n % 10
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)

theorem mySumDigits_zero : mySumDigits 0 = 0 := by
  conv_lhs => unfold mySumDigits
  exact dif_pos rfl

theorem mySumDigits_pos {n : Nat} (h : n ≠ 0) :
    mySumDigits n = mySumDigits (n / 10) + n % 10 := by
  conv_lhs => unfold mySumDigits
  exact dif_neg h

/-! ## Unit tests -/

example : mySumDigits 123 = 6 := by native_decide
example : mySumDigits 0 = 0 := by native_decide
example : mySumDigits 5 = 5 := by native_decide
example : mySumDigits 9999 = 36 := by native_decide

#eval mySumDigits 123
#eval mySumDigits 0
#eval mySumDigits 507

/-! ## Precondition -/

/-- Precondition of `prog`: `n` is a non-negative integer.
    (The Python `isinstance(n, int)` check is captured by using `Int`.) -/
def Pre (n : Int) : Prop := 0 ≤ n

example : Pre (123 : Int) := by unfold Pre; decide
example : ¬ Pre (-1 : Int) := by unfold Pre; decide

/-! ## Properties -/

/-- At `0` the digit sum is `0`. -/
def sumDigits_zero_prop : Prop := mySumDigits 0 = 0

/-- A single digit is returned unchanged. -/
def sumDigits_single_prop (n : Nat) : Prop := n < 10 → mySumDigits n = n

/-- Appending a decimal digit multiplies-and-adds as expected. -/
def sumDigits_concat_prop (a b : Nat) : Prop :=
  b < 10 → mySumDigits (10 * a + b) = mySumDigits a + b

/-- The digit sum never exceeds the number itself. -/
def sumDigits_le_prop (n : Nat) : Prop := mySumDigits n ≤ n

/-- Casting out nines: the digit sum is congruent to `n` modulo `9`. -/
def sumDigits_mod9_prop (n : Nat) : Prop := mySumDigits n % 9 = n % 9

theorem sumDigits_zero_thm : sumDigits_zero_prop := mySumDigits_zero

theorem sumDigits_single_thm (n : Nat) : sumDigits_single_prop n := by
  unfold sumDigits_single_prop
  intro h
  by_cases h0 : n = 0
  · subst h0; exact mySumDigits_zero
  · have hd : n / 10 = 0 := Nat.div_eq_of_lt h
    have hm : n % 10 = n := Nat.mod_eq_of_lt h
    rw [mySumDigits_pos h0, hd, hm, mySumDigits_zero, Nat.zero_add]

theorem sumDigits_concat_thm (a b : Nat) : sumDigits_concat_prop a b := by
  unfold sumDigits_concat_prop
  intro hb
  by_cases h0 : 10 * a + b = 0
  · have ha : a = 0 := by omega
    have hb0 : b = 0 := by omega
    rw [ha, hb0, show (10 : Nat) * 0 + 0 = 0 from rfl, mySumDigits_zero]
  · have hd : (10 * a + b) / 10 = a := by omega
    have hm : (10 * a + b) % 10 = b := by omega
    rw [mySumDigits_pos h0, hd, hm]

theorem sumDigits_le_thm (n : Nat) : sumDigits_le_prop n := by
  induction n using Nat.strong_induction_on
  next n ih =>
  by_cases h : n = 0
  · subst h
    simp [sumDigits_le_prop, mySumDigits_zero]
  · have hlt : n / 10 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)
    have ihd := ih (n / 10) hlt
    simp only [sumDigits_le_prop] at ihd ⊢
    rw [mySumDigits_pos h]
    have h10 : n = 10 * (n / 10) + n % 10 := (Nat.div_add_mod n 10).symm
    omega

theorem sumDigits_mod9_thm (n : Nat) : sumDigits_mod9_prop n := by
  induction n using Nat.strong_induction_on
  next n ih =>
  by_cases h : n = 0
  · subst h
    simp [sumDigits_mod9_prop, mySumDigits_zero]
  · have hlt : n / 10 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)
    have ihd := ih (n / 10) hlt
    simp only [sumDigits_mod9_prop] at ihd ⊢
    rw [mySumDigits_pos h, Nat.add_mod, ihd]
    have h10 : n = 10 * (n / 10) + n % 10 := (Nat.div_add_mod n 10).symm
    conv_rhs => rw [h10]
    omega

/-! ## Postcondition -/

/-- Postcondition of `prog` on input `n` with result `r`:
    the result is the digit sum, and it satisfies the stated properties. -/
def Post_prop (n : Int) (r : Nat) : Prop :=
  r = mySumDigits n.toNat ∧
  sumDigits_le_prop n.toNat ∧
  sumDigits_mod9_prop n.toNat

/-! ## Property-based tests -/

-- PBT for `sumDigits_zero_prop` (bounded; concerns the single input `0`)
example : (List.range 1).all (fun n => decide (mySumDigits n = 0)) = true := by
  native_decide

-- PBT for `sumDigits_single_prop` (randomized and exhaustive-bounded)
#eval Plausible.Testable.check (∀ n : Nat, mySumDigits (n % 10) = n % 10)
example : (List.range 10).all (fun n => decide (mySumDigits n = n)) = true := by
  native_decide

-- PBT for `sumDigits_concat_prop`
#eval Plausible.Testable.check
  (∀ a b : Nat, mySumDigits (10 * a + b % 10) = mySumDigits a + b % 10)
example : ((List.range 60).product (List.range 10)).all
    (fun (a, b) => decide (mySumDigits (10 * a + b) = mySumDigits a + b)) = true := by
  native_decide

-- PBT for `sumDigits_le_prop`
#eval Plausible.Testable.check (∀ n : Nat, mySumDigits n ≤ n)
example : (List.range 500).all (fun n => decide (mySumDigits n ≤ n)) = true := by
  native_decide

-- PBT for `sumDigits_mod9_prop`
#eval Plausible.Testable.check (∀ n : Nat, mySumDigits n % 9 = n % 9)
example : (List.range 500).all (fun n => decide (mySumDigits n % 9 = n % 9)) = true := by
  native_decide

-- PBT for `Post_prop` (executable Boolean form on non-negative inputs)
example : (List.range 300).all (fun n =>
    let r := mySumDigits n
    decide (r = mySumDigits (Int.toNat (n : Int))) &&
    decide (r ≤ n) &&
    decide (r % 9 = n % 9)) = true := by
  native_decide

/-! ## The Python `prog` with its `ValueError`, modelled by `Except` -/

/-- Python's `prog`: returns the digit sum, raises `ValueError` when the
    precondition is violated. -/
def prog (n : Int) : Except String Nat :=
  if 0 ≤ n then .ok (mySumDigits n.toNat)
  else .error s!"Require non-negative integer (got n={n})"

theorem prog_ok {n : Int} (h : Pre n) : prog n = .ok (mySumDigits n.toNat) := by
  unfold Pre at h
  unfold prog
  rw [if_pos h]

theorem prog_error {n : Int} (h : ¬ Pre n) : ∃ msg, prog n = .error msg := by
  unfold Pre at h
  unfold prog
  exact ⟨s!"Require non-negative integer (got n={n})", if_neg h⟩

example : (prog 123).toOption = some 6 := by native_decide
example : (prog 0).toOption = some 0 := by native_decide
example : (prog (-1)).toOption = none := by native_decide

/-! ## Correctness theorem: Pre → Post -/

theorem mySumDigits_correct {n : Int} (_hpre : Pre n) :
    Post_prop n (mySumDigits n.toNat) := by
  unfold Post_prop
  exact ⟨rfl, sumDigits_le_thm _, sumDigits_mod9_thm _⟩

/-! ## Imperative implementation -/

/-- Tail-recursive loop performing exactly the state updates of the Python
    `while`-loop: `total += m % 10; m //= 10` until `m = 0`. -/
def sumLoop (m acc : Nat) : Nat :=
  if h : m = 0 then acc
  else sumLoop (m / 10) (acc + m % 10)
termination_by m
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)

theorem sumLoop_zero (acc : Nat) : sumLoop 0 acc = acc := by
  conv_lhs => unfold sumLoop
  exact dif_pos rfl

theorem sumLoop_pos {m : Nat} (h : m ≠ 0) (acc : Nat) :
    sumLoop m acc = sumLoop (m / 10) (acc + m % 10) := by
  conv_lhs => unfold sumLoop
  exact dif_neg h

/-- Imperative implementation using `Id.run` with mutable state. -/
def mySumDigitsImp (n : Nat) : Nat := Id.run do
  let mut total := 0
  let mut m := n
  total := sumLoop m total
  return total

/-! ## Imperative tests -/

example : mySumDigitsImp 123 = 6 := by native_decide
example : mySumDigitsImp 0 = 0 := by native_decide
example : mySumDigitsImp 9999 = 36 := by native_decide

#eval mySumDigitsImp 123
#eval mySumDigitsImp 0

/-! ## Equivalence of the functional and imperative implementations -/

theorem sumLoop_eq (m acc : Nat) : sumLoop m acc = acc + mySumDigits m := by
  induction m using Nat.strong_induction_on generalizing acc
  next m ih =>
  by_cases h : m = 0
  · subst h
    simp [sumLoop_zero, mySumDigits_zero]
  · have hlt : m / 10 < m := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)
    rw [sumLoop_pos h, ih (m / 10) hlt (acc + m % 10), mySumDigits_pos h]
    omega

theorem mySumDigits_imp_eq (n : Nat) : mySumDigitsImp n = mySumDigits n := by
  rw [show mySumDigitsImp n = sumLoop n 0 from rfl, sumLoop_eq, Nat.zero_add]

end MySumDigits20
