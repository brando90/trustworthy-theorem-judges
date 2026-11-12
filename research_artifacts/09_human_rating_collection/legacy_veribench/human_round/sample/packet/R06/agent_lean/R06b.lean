import Mathlib

/-!
# Sum of digits of a non-negative integer

This file formalizes the Python program

```python
def pre(n: int) -> bool:
    return isinstance(n, int) and n >= 0

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

The Python function is total on the set of non-negative integers, which is
modelled by the pre-condition `Pre n := 0 ≤ n` on `ℤ`.  Inputs violating the
pre-condition raise `ValueError` in Python; here they are simply outside the
domain on which any specification is claimed.

Contents:
* `sumDigits` : the functional (recursive) implementation on `ℕ`;
* `prog`      : the `ℤ`-level entry point matching the Python signature;
* a collection of properties (`*_prop`) with proofs (`*_thm`);
* `Post_prop` : the post-condition, and `correctness_thm : Pre n → Post_prop n`;
* `sumDigitsImp` / `progImp` : an imperative `Id.run do` version with mutable
  state and a loop, together with the equivalence theorem.
-/

namespace MySumDigits

/-! ## Functional implementation -/

/-- Sum of the decimal digits of a natural number. -/
def sumDigits (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else n % 10 + sumDigits (n / 10)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)

/-- The pre-condition: `n` is a non-negative integer. -/
def Pre (n : ℤ) : Prop := 0 ≤ n

instance (n : ℤ) : Decidable (Pre n) := by unfold Pre; infer_instance

/-- The Python entry point `prog`, on `ℤ`. For inputs satisfying `Pre` this is
the sum of the decimal digits; the value on negative inputs is unspecified
(Python raises `ValueError` there). -/
def prog (n : ℤ) : ℤ := (sumDigits n.toNat : ℤ)

/-! ## Basic unfolding lemmas -/

@[simp] theorem sumDigits_zero : sumDigits 0 = 0 := by
  rw [sumDigits]; simp

theorem sumDigits_step {n : ℕ} (h : 0 < n) :
    sumDigits n = n % 10 + sumDigits (n / 10) := by
  rw [sumDigits.eq_def]
  simp [h.ne']

/-! ## Unit tests -/

-- Basic unit test: `candidate(123) == 6`
example : prog 123 = 6 := by native_decide

-- Edge unit test: `candidate(0) == 0`
example : prog 0 = 0 := by native_decide

-- Pre-violations (Python raises `ValueError`): `-1` is outside the domain.
example : ¬ Pre (-1) := by decide

example : sumDigits 9999 = 36 := by native_decide
example : sumDigits 7 = 7 := by native_decide
example : sumDigits 1000000 = 1 := by native_decide

#eval prog 123          -- 6
#eval prog 0            -- 0
#eval sumDigits 987654321 -- 45

/-! ## Properties -/

/-- `sumDigits` agrees with the sum of `Nat.digits 10`. -/
theorem sumDigits_eq_digits_sum (n : ℕ) : sumDigits n = (Nat.digits 10 n).sum := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · rw [sumDigits_step h, Nat.digits_def' (by norm_num) h, List.sum_cons,
        ih _ (Nat.div_lt_self h (by norm_num))]

/-- A positive number has a positive digit sum. -/
theorem sumDigits_pos {n : ℕ} (h : 0 < n) : 0 < sumDigits n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [sumDigits_step h]
    rcases Nat.eq_zero_or_pos (n / 10) with hd | hd
    · have : n % 10 = n := by omega
      omega
    · have := ih _ (Nat.div_lt_self h (by norm_num)) hd
      omega

/-- The digit sum never exceeds the number itself. -/
theorem sumDigits_le (n : ℕ) : sumDigits n ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have := ih (n / 10) (Nat.div_lt_self h (by norm_num))
      rw [sumDigits_step h]
      omega

/-- Single-digit numbers are their own digit sum. -/
theorem sumDigits_of_lt_ten {n : ℕ} (h : n < 10) : sumDigits n = n := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simp
  · rw [sumDigits_step h0]
    have h1 : n / 10 = 0 := by omega
    have h2 : n % 10 = n := by omega
    simp [h1, h2]

/-- Casting-out-nines: the digit sum is congruent to the number mod `9`. -/
theorem sumDigits_mod_nine (n : ℕ) : sumDigits n % 9 = n % 9 := by
  have := Nat.modEq_digits_sum 9 10 (by norm_num) n
  rw [sumDigits_eq_digits_sum]
  exact this.symm

/-! ### `ℤ`-level property statements -/

/-- `prog 0 = 0`. -/
def zero_prop : Prop := prog 0 = 0

theorem zero_thm : zero_prop := by
  simp [zero_prop, prog]

/-- Single digit inputs return themselves. -/
def single_digit_prop : Prop := ∀ n : ℤ, Pre n → n < 10 → prog n = n

theorem single_digit_thm : single_digit_prop := by
  intro n hn hlt
  unfold Pre at hn
  have h : n.toNat < 10 := by omega
  simp only [prog, sumDigits_of_lt_ten h]
  omega

/-- The result is always non-negative. -/
def nonneg_prop : Prop := ∀ n : ℤ, Pre n → 0 ≤ prog n

theorem nonneg_thm : nonneg_prop := by
  intro n _
  simp [prog]

/-- The result never exceeds the input. -/
def le_self_prop : Prop := ∀ n : ℤ, Pre n → prog n ≤ n

theorem le_self_thm : le_self_prop := by
  intro n hn
  have h := sumDigits_le n.toNat
  have : ((sumDigits n.toNat : ℤ)) ≤ (n.toNat : ℤ) := by exact_mod_cast h
  unfold Pre at hn
  simpa [prog, Int.toNat_of_nonneg hn] using this

/-- The loop invariant, read as a recurrence: this is exactly one iteration of
the Python `while` loop (`total += n % 10; n //= 10`). -/
def step_prop : Prop := ∀ n : ℤ, Pre n → 0 < n → prog n = n % 10 + prog (n / 10)

theorem step_thm : step_prop := by
  intro n _ hp
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.toNat, by omega⟩
  have hm : 0 < m := by exact_mod_cast hp
  have h1 : ((m : ℤ)) / 10 = ((m / 10 : ℕ) : ℤ) := by omega
  have h2 : ((m : ℤ)) % 10 = ((m % 10 : ℕ) : ℤ) := by omega
  simp only [prog, h1, h2, Int.toNat_natCast]
  rw [sumDigits_step hm]
  push_cast
  ring

/-- The result is `0` exactly on input `0`. -/
def eq_zero_iff_prop : Prop := ∀ n : ℤ, Pre n → (prog n = 0 ↔ n = 0)

theorem eq_zero_iff_thm : eq_zero_iff_prop := by
  intro n hn
  unfold Pre at hn
  constructor
  · intro h
    by_contra hne
    have hpos : 0 < n.toNat := by omega
    have := sumDigits_pos hpos
    simp only [prog] at h
    omega
  · rintro rfl
    simp [prog]

/-- Casting out nines, at the `ℤ` level. -/
def mod_nine_prop : Prop := ∀ n : ℤ, Pre n → prog n % 9 = n % 9

theorem mod_nine_thm : mod_nine_prop := by
  intro n hn
  unfold Pre at hn
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.toNat, by omega⟩
  have h := sumDigits_mod_nine m
  simp only [prog, Int.toNat_natCast]
  omega

/-- `prog` computes the sum of the base-10 digits of its argument. -/
def digits_sum_prop : Prop :=
  ∀ n : ℤ, Pre n → prog n = ((Nat.digits 10 n.toNat).sum : ℤ)

theorem digits_sum_thm : digits_sum_prop := by
  intro n _
  simp [prog, sumDigits_eq_digits_sum]

/-! ## Post-condition and correctness -/

/-- The post-condition: the conjunction of all specified properties. -/
def Post_prop (n : ℤ) : Prop :=
  0 ≤ prog n ∧
  prog n ≤ n ∧
  prog n = ((Nat.digits 10 n.toNat).sum : ℤ) ∧
  (n < 10 → prog n = n) ∧
  (0 < n → prog n = n % 10 + prog (n / 10)) ∧
  (prog n = 0 ↔ n = 0) ∧
  prog n % 9 = n % 9

/-- Correctness: on every input satisfying the pre-condition, the
post-condition holds. -/
theorem correctness_thm : ∀ n : ℤ, Pre n → Post_prop n := by
  intro n hn
  exact ⟨nonneg_thm n hn, le_self_thm n hn, digits_sum_thm n hn,
    fun h => single_digit_thm n hn h, fun h => step_thm n hn h,
    eq_zero_iff_thm n hn, mod_nine_thm n hn⟩

/-! ## Imperative implementation

A transcription of the Python `while` loop with mutable state (`n` and
`total`).  Lean's `for` loop is bounded, so the loop runs
`Nat.log 10 n0 + 1` times -- exactly the number of decimal digits of `n0`,
which is precisely how many iterations the Python `while n > 0` loop performs
(and one harmless extra no-op round when `n` has already reached `0`, since
`0 % 10 = 0` and `0 / 10 = 0`). -/

def sumDigitsImp (n0 : ℕ) : ℕ := Id.run do
  let mut n := n0
  let mut total := 0
  for _ in List.range (Nat.log 10 n0 + 1) do
    total := total + n % 10
    n := n / 10
  return total

/-- The imperative entry point matching the Python signature. -/
def progImp (n : ℤ) : ℤ := Id.run do
  let r := sumDigitsImp n.toNat
  return (r : ℤ)

/-! ### Imperative unit tests -/

example : progImp 123 = 6 := by native_decide
example : progImp 0 = 0 := by native_decide
example : sumDigitsImp 9999 = 36 := by native_decide
example : sumDigitsImp 1000000 = 1 := by native_decide
example : sumDigitsImp 987654321 = 45 := by native_decide

#eval progImp 123            -- 6
#eval progImp 0              -- 0
#eval sumDigitsImp 987654321 -- 45

/-! ### Equivalence -/

/-- The loop invariant: running the loop body over a list of length at least
the number of digits of `n` accumulates exactly `sumDigits n` into `total`. -/
private theorem foldl_loop_body (l : List ℕ) :
    ∀ n t : ℕ, n < 10 ^ l.length →
      (l.foldl (fun (s : MProd ℕ ℕ) _ => ⟨s.1 / 10, s.2 + s.1 % 10⟩) ⟨n, t⟩).2
        = t + sumDigits n := by
  induction l with
  | nil =>
      intro n t h
      simp at h
      subst h
      simp
  | cons a l ih =>
      intro n t h
      have hle : n / 10 < 10 ^ l.length := by
        simp only [List.length_cons, pow_succ] at h
        omega
      have hres := ih (n / 10) (t + n % 10) hle
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0
        simpa using hres
      · simp only [List.foldl_cons]
        rw [hres, sumDigits_step h0]
        omega

/-- The imperative loop computes the same value as the functional version. -/
theorem sumDigitsImp_eq (n : ℕ) : sumDigitsImp n = sumDigits n := by
  have h := foldl_loop_body (List.range (Nat.log 10 n + 1)) n 0
    (by simpa using Nat.lt_pow_succ_log_self (by norm_num : 1 < 10) n)
  simpa [sumDigitsImp] using h

/-- Equivalence theorem: the functional and imperative versions agree on every
input. -/
theorem prog_eq_progImp : ∀ n : ℤ, progImp n = prog n := by
  intro n
  simp [progImp, prog, sumDigitsImp_eq]

end MySumDigits
