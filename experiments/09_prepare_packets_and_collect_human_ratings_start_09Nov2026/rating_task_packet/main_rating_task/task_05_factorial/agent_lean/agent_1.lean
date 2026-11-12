import Mathlib

/-!
# `16_MyFactorial`: factorial of a natural number

Lean 4 formalization of the Python program `prog(n: int) -> int`, which returns `n!`
for a non-negative integer `n` and raises `ValueError` otherwise.

* `myFactorial : Nat → Nat` is the mathematical core (`0! = 1`, `(n+1)! = (n+1) · n!`).
* `prog : Int → Except String Int` is the Python-level program: the input is a Python
  `int` (Lean `Int`); a negative input yields `Except.error msg` (the `ValueError`
  with the program's message), and a non-negative input yields `Except.ok n!`.
  The `isinstance(n, int)` half of the Python precondition is enforced statically by
  the type `Int` (a `float` such as `3.14` cannot be passed in Lean).
* `progImp` is an imperative version with a mutable accumulator and a `for` loop over
  `range(1, n + 1)`, exactly like the Python source; it is proved equal to `prog`.
-/

namespace «16_MyFactorial»

/-! ## Functional implementation -/

/-- Mathematical core: factorial on naturals, by structural recursion. -/
def myFactorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * myFactorial n

/-- The message carried by the `ValueError` raised by the Python program. -/
def errMsg (n : Int) : String :=
  s!"Input must be a non-negative integer (got n={n})"

/-- The Python `prog`: `n!` for a non-negative `int`, `ValueError` (as `Except.error`)
for a negative one. -/
def prog (n : Int) : Except String Int :=
  if n < 0 then
    .error (errMsg n)
  else
    .ok (myFactorial n.toNat : Int)

-- `Except` has no `DecidableEq` instance in core; derive one so results can be
-- compared in tests.
deriving instance DecidableEq for Except

/-! ## Unit tests -/

-- Basic unit test from the Python `check`: `candidate(3) == 6`
example : prog 3 = .ok 6 := by native_decide
-- Edge unit test from the Python `check`: `candidate(0) == 1`
example : prog 0 = .ok 1 := by native_decide
example : prog 1 = .ok 1 := by native_decide
example : prog 5 = .ok 120 := by native_decide
example : prog 10 = .ok 3628800 := by native_decide
-- Negative input raises `ValueError` (`-1` is the Python `bad_inputs` case; `3.14`
-- is excluded statically by the type `Int`).
example : prog (-1) = .error (errMsg (-1)) := by native_decide
example : (prog (-1)).toBool = false := by native_decide
example : (prog (-7)).toBool = false := by native_decide
example : myFactorial 0 = 1 := by native_decide
example : myFactorial 1 = 1 := by native_decide
example : myFactorial 3 = 6 := by native_decide
example : myFactorial 6 = 720 := by native_decide

#eval prog 3        -- Except.ok 6
#eval prog 0        -- Except.ok 1
#eval prog (-1)     -- Except.error "Input must be a non-negative integer (got n=-1)"
#eval myFactorial 20

/-! ## Pre-condition -/

/-- Python `pre`: the input is a non-negative integer. (Being an integer is enforced
by the type `Int`.) -/
def Pre (n : Int) : Prop := 0 ≤ n

/-! ## Properties of the mathematical core `myFactorial` -/

/-- `factorial(0) = 1` by definition. -/
def myFactorial_zero_prop : Prop := myFactorial 0 = 1

theorem myFactorial_zero_thm : myFactorial_zero_prop := rfl

/-- `factorial(1) = 1`. -/
def myFactorial_one_prop : Prop := myFactorial 1 = 1

theorem myFactorial_one_thm : myFactorial_one_prop := rfl

/-- Recurrence `(n+1)! = (n+1) · n!`. -/
def myFactorial_succ_prop (n : Nat) : Prop := myFactorial (n + 1) = (n + 1) * myFactorial n

theorem myFactorial_succ_thm (n : Nat) : myFactorial_succ_prop n := rfl

/-- The core agrees with Mathlib's `Nat.factorial`. -/
def myFactorial_eq_factorial_prop (n : Nat) : Prop := myFactorial n = n.factorial

theorem myFactorial_eq_factorial_thm (n : Nat) : myFactorial_eq_factorial_prop n := by
  unfold myFactorial_eq_factorial_prop
  induction n with
  | zero => rfl
  | succ k ih => rw [myFactorial, ih, Nat.factorial_succ]

/-- The core equals the Python loop `result = 1; for i in range(1, n+1): result *= i`. -/
def myFactorial_eq_foldl_prop (n : Nat) : Prop :=
  myFactorial n = (List.range' 1 n).foldl (· * ·) 1

/-- Fold form of the Python loop with an arbitrary starting accumulator. -/
theorem foldl_range'_mul_nat (n acc : Nat) :
    (List.range' 1 n).foldl (· * ·) acc = acc * myFactorial n := by
  induction n generalizing acc with
  | zero => simp [myFactorial]
  | succ k ih =>
    rw [List.range'_1_concat, List.foldl_append, ih]
    simp [myFactorial]
    ring

theorem myFactorial_eq_foldl_thm (n : Nat) : myFactorial_eq_foldl_prop n := by
  unfold myFactorial_eq_foldl_prop
  rw [foldl_range'_mul_nat, one_mul]

/-- Factorials are positive. -/
def myFactorial_pos_prop (n : Nat) : Prop := 0 < myFactorial n

theorem myFactorial_pos_thm (n : Nat) : myFactorial_pos_prop n := by
  unfold myFactorial_pos_prop
  have h : myFactorial n = n.factorial := myFactorial_eq_factorial_thm n
  rw [h]
  exact Nat.factorial_pos n

/-- `n ≤ n!`. -/
def myFactorial_self_le_prop (n : Nat) : Prop := n ≤ myFactorial n

theorem myFactorial_self_le_thm (n : Nat) : myFactorial_self_le_prop n := by
  unfold myFactorial_self_le_prop
  have h : myFactorial n = n.factorial := myFactorial_eq_factorial_thm n
  rw [h]
  exact Nat.self_le_factorial n

/-- Factorial is monotone. -/
def myFactorial_mono_prop (m n : Nat) : Prop := m ≤ n → myFactorial m ≤ myFactorial n

theorem myFactorial_mono_thm (m n : Nat) : myFactorial_mono_prop m n := by
  unfold myFactorial_mono_prop
  intro hmn
  have hm : myFactorial m = m.factorial := myFactorial_eq_factorial_thm m
  have hn : myFactorial n = n.factorial := myFactorial_eq_factorial_thm n
  rw [hm, hn]
  exact Nat.factorial_le hmn

/-- `n ∣ n!` for `n ≥ 1`. -/
def myFactorial_dvd_prop (n : Nat) : Prop := 0 < n → n ∣ myFactorial n

theorem myFactorial_dvd_thm (n : Nat) : myFactorial_dvd_prop n := by
  unfold myFactorial_dvd_prop
  intro hn
  have h : myFactorial n = n.factorial := myFactorial_eq_factorial_thm n
  rw [h]
  exact Nat.dvd_factorial hn le_rfl

/-! ## Properties of the Python-level program `prog` -/

/-- On admissible inputs the program returns `ok` of the core factorial. -/
def prog_ok_prop (n : Int) : Prop := 0 ≤ n → prog n = .ok (myFactorial n.toNat : Int)

theorem prog_ok_thm (n : Int) : prog_ok_prop n := by
  unfold prog_ok_prop
  intro h
  have h' : ¬ n < 0 := not_lt.mpr h
  simp [prog, h']

/-- On admissible inputs the program returns `ok n!` (Mathlib's factorial). -/
def prog_eq_factorial_prop (n : Int) : Prop := 0 ≤ n → prog n = .ok (n.toNat.factorial : Int)

theorem prog_eq_factorial_thm (n : Int) : prog_eq_factorial_prop n := by
  unfold prog_eq_factorial_prop
  intro h
  have h1 : prog n = .ok (myFactorial n.toNat : Int) := prog_ok_thm n h
  have h2 : myFactorial n.toNat = n.toNat.factorial := myFactorial_eq_factorial_thm n.toNat
  rw [h1, h2]

/-- A negative input raises `ValueError` with the program's message. -/
def prog_error_prop (n : Int) : Prop := n < 0 → prog n = .error (errMsg n)

theorem prog_error_thm (n : Int) : prog_error_prop n := by
  unfold prog_error_prop
  intro h
  simp [prog, h]

/-- The program returns normally exactly when the precondition holds. -/
def prog_ok_iff_prop (n : Int) : Prop := (∃ r, prog n = .ok r) ↔ Pre n

theorem prog_ok_iff_thm (n : Int) : prog_ok_iff_prop n := by
  unfold prog_ok_iff_prop Pre
  constructor
  · rintro ⟨r, hr⟩
    by_contra hneg
    push_neg at hneg
    have he : prog n = .error (errMsg n) := prog_error_thm n hneg
    rw [he] at hr
    exact Except.noConfusion hr
  · intro h
    exact ⟨_, prog_ok_thm n h⟩

/-- `factorial(0) = 1` at the program level. -/
def prog_zero_prop : Prop := prog 0 = .ok 1

theorem prog_zero_thm : prog_zero_prop := by
  unfold prog_zero_prop
  simp [prog, myFactorial]

/-- `factorial(1) = 1` at the program level. -/
def prog_one_prop : Prop := prog 1 = .ok 1

theorem prog_one_thm : prog_one_prop := by
  unfold prog_one_prop
  simp [prog, myFactorial]

/-- Recurrence at the program level: `prog (n+1) = (n+1) · prog n` on admissible inputs. -/
def prog_succ_prop (n : Int) : Prop :=
  0 ≤ n → prog (n + 1) = (prog n).map (fun r => (n + 1) * r)

theorem prog_succ_thm (n : Int) : prog_succ_prop n := by
  unfold prog_succ_prop
  intro h
  have h1 : 0 ≤ n + 1 := by omega
  have e0 : prog n = .ok (myFactorial n.toNat : Int) := prog_ok_thm n h
  have e1 : prog (n + 1) = .ok (myFactorial (n + 1).toNat : Int) := prog_ok_thm (n + 1) h1
  have ht : (n + 1).toNat = n.toNat + 1 := by omega
  rw [e0, e1, ht, myFactorial]
  simp only [Except.map]
  push_cast
  rw [Int.toNat_of_nonneg h]

/-- The result is positive on admissible inputs. -/
def prog_pos_prop (n : Int) : Prop := 0 ≤ n → ∃ r, prog n = .ok r ∧ 0 < r

theorem prog_pos_thm (n : Int) : prog_pos_prop n := by
  unfold prog_pos_prop
  intro h
  refine ⟨_, prog_ok_thm n h, ?_⟩
  have hp : 0 < myFactorial n.toNat := myFactorial_pos_thm n.toNat
  exact_mod_cast hp

/-- `n ≤ n!` at the program level. -/
def prog_self_le_prop (n : Int) : Prop := 0 ≤ n → ∃ r, prog n = .ok r ∧ n ≤ r

theorem prog_self_le_thm (n : Int) : prog_self_le_prop n := by
  unfold prog_self_le_prop
  intro h
  refine ⟨_, prog_ok_thm n h, ?_⟩
  have hle : n.toNat ≤ myFactorial n.toNat := myFactorial_self_le_thm n.toNat
  calc n = ((n.toNat : Nat) : Int) := (Int.toNat_of_nonneg h).symm
    _ ≤ (myFactorial n.toNat : Int) := by exact_mod_cast hle

/-- `n ∣ n!` for positive `n` at the program level. -/
def prog_dvd_prop (n : Int) : Prop := 0 < n → ∃ r, prog n = .ok r ∧ n ∣ r

theorem prog_dvd_thm (n : Int) : prog_dvd_prop n := by
  unfold prog_dvd_prop
  intro h
  refine ⟨_, prog_ok_thm n (le_of_lt h), ?_⟩
  have hd : n.toNat ∣ myFactorial n.toNat := myFactorial_dvd_thm n.toNat (by omega)
  have hc : ((n.toNat : Nat) : Int) ∣ (myFactorial n.toNat : Int) := Int.natCast_dvd_natCast.mpr hd
  rwa [Int.toNat_of_nonneg (le_of_lt h)] at hc

/-- Monotonicity at the program level. -/
def prog_mono_prop (m n : Int) : Prop :=
  0 ≤ m → m ≤ n → ∃ a b, prog m = .ok a ∧ prog n = .ok b ∧ a ≤ b

theorem prog_mono_thm (m n : Int) : prog_mono_prop m n := by
  unfold prog_mono_prop
  intro hm hmn
  refine ⟨_, _, prog_ok_thm m hm, prog_ok_thm n (le_trans hm hmn), ?_⟩
  have ht : m.toNat ≤ n.toNat := by omega
  have hle : myFactorial m.toNat ≤ myFactorial n.toNat := myFactorial_mono_thm m.toNat n.toNat ht
  exact_mod_cast hle

/-! ## Post-condition -/

/-- Post-condition relating the input `n` to the result `r` of the program (on admissible
inputs): the result is `ok n!`, it agrees with the core, it is positive, at least `n`,
divisible by `n` when `n > 0`, and the two edge cases hold. -/
def Post_prop (n : Int) (r : Except String Int) : Prop :=
  r = .ok (n.toNat.factorial : Int) ∧
  r = .ok (myFactorial n.toNat : Int) ∧
  (∃ v, r = .ok v ∧ 0 < v ∧ n ≤ v ∧ (0 < n → n ∣ v)) ∧
  (n = 0 → r = .ok 1) ∧
  (n = 1 → r = .ok 1)

/-! ## Property-based tests -/

/-- Executable form of "the result is `ok v` with `p v`" (for the existential properties). -/
def okSat (p : Int → Bool) : Except String Int → Bool
  | .ok v => p v
  | .error _ => false

/-- Executable Boolean form of `Post_prop n (prog n)`. -/
def postCheck (n : Int) : Bool :=
  decide (prog n = .ok (n.toNat.factorial : Int)) &&
  decide (prog n = .ok (myFactorial n.toNat : Int)) &&
  okSat (fun v => decide (0 < v) && decide (n ≤ v) && decide (0 < n → n ∣ v)) (prog n) &&
  decide (n = 0 → prog n = .ok 1) &&
  decide (n = 1 → prog n = .ok 1)

-- Core properties (randomized)
#eval Plausible.Testable.check (∀ n : Nat, myFactorial (n + 1) = (n + 1) * myFactorial n)
#eval Plausible.Testable.check (∀ n : Nat, myFactorial n = n.factorial)
#eval Plausible.Testable.check (∀ n : Nat, myFactorial n = (List.range' 1 n).foldl (· * ·) 1)
#eval Plausible.Testable.check (∀ n : Nat, 0 < myFactorial n)
#eval Plausible.Testable.check (∀ n : Nat, n ≤ myFactorial n)
#eval Plausible.Testable.check (∀ m n : Nat, m ≤ n → myFactorial m ≤ myFactorial n)
-- positive inputs written as `k + 1` so no sample is discarded
#eval Plausible.Testable.check (∀ k : Nat, (k + 1) ∣ myFactorial (k + 1))

-- Program-level properties (randomized)
#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n → prog n = .ok (myFactorial n.toNat : Int))
#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n → prog n = .ok (n.toNat.factorial : Int))
-- negative inputs, written without a guard so no sample is discarded
#eval Plausible.Testable.check
  (∀ k : Nat, prog (-(k : Int) - 1) = .error (errMsg (-(k : Int) - 1)))
#eval Plausible.Testable.check (∀ n : Int, (prog n).toBool = decide (0 ≤ n))
#eval Plausible.Testable.check
  (∀ n : Int, 0 ≤ n → prog (n + 1) = (prog n).map (fun r => (n + 1) * r))
#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n → okSat (fun v => decide (0 < v)) (prog n) = true)
#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n → okSat (fun v => decide (n ≤ v)) (prog n) = true)
-- positive inputs written as `k + 1`, and `m ≤ n` written as `n = m + d`, so no sample is discarded
#eval Plausible.Testable.check
  (∀ k : Nat, okSat (fun v => decide (((k : Int) + 1) ∣ v)) (prog ((k : Int) + 1)) = true)
#eval Plausible.Testable.check
  (∀ m d : Nat,
    okSat (fun a => okSat (fun b => decide (a ≤ b)) (prog ((m : Int) + (d : Int)))) (prog (m : Int)) = true)
-- Post-condition (randomized)
#eval Plausible.Testable.check (∀ n : Int, 0 ≤ n → postCheck n = true)

-- Bounded / exhaustive small cases
example : (List.range 30).all (fun n => myFactorial n == n.factorial) = true := by native_decide
example : (List.range 30).all (fun n => myFactorial (n + 1) == (n + 1) * myFactorial n) = true := by
  native_decide
example : (List.range 30).all (fun n => myFactorial n == (List.range' 1 n).foldl (· * ·) 1) = true := by
  native_decide
example : (List.range 30).all (fun n => decide (0 < myFactorial n) && decide (n ≤ myFactorial n)) = true := by
  native_decide
example : (List.range 30).all (fun n => n == 0 || decide (n ∣ myFactorial n)) = true := by native_decide
example : (List.range 30).all (fun n => postCheck (n : Int)) = true := by native_decide
example : (List.range 20).all (fun m => (List.range 20).all (fun n =>
    !(decide (m ≤ n)) || okSat (fun a => okSat (fun b => decide (a ≤ b)) (prog (n : Int))) (prog (m : Int))))
    = true := by native_decide
example : (List.range 30).all (fun n => prog (n : Int) == .ok (n.factorial : Int)) = true := by
  native_decide
example : (List.range 30).all
    (fun k => prog (-(k : Int) - 1) == .error (errMsg (-(k : Int) - 1))) = true := by
  native_decide
example : (List.range 30).all (fun k => (prog (-(k : Int) - 1)).toBool == false) = true := by
  native_decide
example : (List.range 30).all
    (fun n => prog ((n : Int) + 1) == (prog (n : Int)).map (fun r => ((n : Int) + 1) * r)) = true := by
  native_decide

/-! ## Correctness -/

/-- `Pre → Post`: on every admissible input the program satisfies the post-condition. -/
theorem correctness_thm (n : Int) (h : Pre n) : Post_prop n (prog n) := by
  unfold Pre at h
  unfold Post_prop
  refine ⟨prog_eq_factorial_thm n h, prog_ok_thm n h, ?_, ?_, ?_⟩
  · refine ⟨_, prog_ok_thm n h, ?_, ?_, ?_⟩
    · have hp : 0 < myFactorial n.toNat := myFactorial_pos_thm n.toNat
      exact_mod_cast hp
    · have hle : n.toNat ≤ myFactorial n.toNat := myFactorial_self_le_thm n.toNat
      calc n = ((n.toNat : Nat) : Int) := (Int.toNat_of_nonneg h).symm
        _ ≤ (myFactorial n.toNat : Int) := by exact_mod_cast hle
    · intro hpos
      have hd : n.toNat ∣ myFactorial n.toNat := myFactorial_dvd_thm n.toNat (by omega)
      have hc : ((n.toNat : Nat) : Int) ∣ (myFactorial n.toNat : Int) :=
        Int.natCast_dvd_natCast.mpr hd
      rwa [Int.toNat_of_nonneg h] at hc
  · intro h0
    subst h0
    exact prog_zero_thm
  · intro h1
    subst h1
    exact prog_one_thm

/-- Total specification: admissible inputs satisfy the post-condition, inadmissible
inputs raise `ValueError` with the program's message. -/
theorem prog_spec_thm (n : Int) :
    (Pre n → Post_prop n (prog n)) ∧ (¬ Pre n → prog n = .error (errMsg n)) := by
  refine ⟨correctness_thm n, ?_⟩
  intro hn
  unfold Pre at hn
  exact prog_error_thm n (by omega)

/-- The Python test suite `check` (the integer cases; `3.14` is excluded by the type). -/
def check_prop : Prop :=
  prog 3 = .ok 6 ∧ prog 0 = .ok 1 ∧ prog (-1) = .error (errMsg (-1))

theorem check_thm : check_prop := by
  unfold check_prop
  refine ⟨?_, ?_, ?_⟩
  · simp [prog, myFactorial]
  · simp [prog, myFactorial]
  · simp [prog]

/-! ## Imperative implementation -/

/-- Imperative version mirroring the Python source line by line: precondition check,
`n == 0` shortcut, then `result = 1; for i in range(1, n + 1): result *= i`. -/
def progImp (n : Int) : Except String Int := Id.run do
  if n < 0 then
    return .error (errMsg n)
  if n == 0 then
    return .ok 1
  let mut result : Int := 1
  for i in List.range' 1 n.toNat do
    result := result * (i : Int)
  return .ok result

/-! ## Imperative tests -/

example : progImp 3 = .ok 6 := by native_decide
example : progImp 0 = .ok 1 := by native_decide
example : progImp 1 = .ok 1 := by native_decide
example : progImp 5 = .ok 120 := by native_decide
example : progImp 10 = .ok 3628800 := by native_decide
example : progImp (-1) = .error (errMsg (-1)) := by native_decide
example : (progImp (-1)).toBool = false := by native_decide

#eval progImp 3
#eval progImp 0
#eval progImp (-1)

#eval Plausible.Testable.check (∀ n : Int, prog n = progImp n)
example : (List.range 30).all (fun n => prog (n : Int) == progImp (n : Int)) = true := by native_decide
example : (List.range 30).all (fun k => prog (-(k : Int) - 1) == progImp (-(k : Int) - 1)) = true := by
  native_decide

/-! ## Equivalence of the functional and imperative implementations -/

/-- The Python loop over `range(1, n + 1)` with an `Int` accumulator computes `acc · n!`. -/
theorem foldl_range'_mul_int (n : Nat) (acc : Int) :
    (List.range' 1 n).foldl (fun (r : Int) (i : Nat) => r * (i : Int)) acc
      = acc * (myFactorial n : Int) := by
  induction n generalizing acc with
  | zero => simp [myFactorial]
  | succ k ih =>
    rw [List.range'_1_concat, List.foldl_append, ih]
    simp [myFactorial]
    ring

/-- Functional and imperative implementations agree on every input (including the
error cases). -/
theorem prog_eq_progImp_thm (n : Int) : prog n = progImp n := by
  by_cases h : n < 0
  · simp [prog, progImp, h]
  · by_cases h0 : n = 0
    · subst h0
      simp [prog, progImp, myFactorial]
    · have h2 : (n == 0) = false := by simpa using h0
      simp [prog, progImp, h, h2, foldl_range'_mul_int]

/-- Consequently the imperative program also satisfies the post-condition. -/
theorem progImp_correct_thm (n : Int) (h : Pre n) : Post_prop n (progImp n) := by
  rw [← prog_eq_progImp_thm]
  exact correctness_thm n h

end «16_MyFactorial»
