import Mathlib

/-!
# 16_MyFactorial

Formalization of the Python `factorial` program.

The Python function `prog` returns `n!` for a non-negative integer `n` and
raises `ValueError` when its precondition (the input is a non-negative
integer) is violated.  This file models:

* `myFactorial` — the functional implementation over `Nat`.
* `Pre` / `pre` — the precondition (`n ≥ 0`) as a `Prop` and as a Boolean.
* `prog` — a total model of the Python program on `Int` returning
  `Except String Nat`, raising the same error message on precondition
  violations.
* Properties of the implementation with proofs, the post-condition
  `Post_prop` as their conjunction, and the correctness theorem `Pre → Post`.
* Property-based tests (randomized via `Plausible` and bounded exhaustive).
* `myFactorialImp` — an imperative implementation using `Id.run` with
  mutable state, plus a proof that it coincides with the functional one.
-/

namespace «16_MyFactorial»

/-! ## Functional implementation -/

/-- Factorial of a natural number (functional implementation). -/
def myFactorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * myFactorial n

-- ### Unit tests

example : myFactorial 0 = 1 := by native_decide
example : myFactorial 1 = 1 := by native_decide
example : myFactorial 3 = 6 := by native_decide
example : myFactorial 5 = 120 := by native_decide

#eval myFactorial 0   -- 1
#eval myFactorial 3   -- 6
#eval myFactorial 10  -- 3628800

/-! ## Precondition -/

/-- Python precondition: the input is a non-negative integer. -/
def Pre (n : Int) : Prop := 0 ≤ n

/-- Boolean (executable) form of `Pre`, matching Python's `pre`. -/
def pre (n : Int) : Bool := decide (0 ≤ n)

example : pre 3 = true := by native_decide
example : pre 0 = true := by native_decide
example : pre (-1) = false := by native_decide

/-! ## The Python program with its error behaviour -/

/-- Total model of the Python program: returns `Except.ok n!` when the
precondition holds and `Except.error msg` (the Python `ValueError`)
otherwise. -/
def prog (n : Int) : Except String Nat :=
  if 0 ≤ n then
    Except.ok (myFactorial n.toNat)
  else
    Except.error s!"Input must be a non-negative integer (got n={n})"

/-- Boolean check: `e` is `Except.ok v`. -/
def isOkWith (e : Except String Nat) (v : Nat) : Bool :=
  match e with
  | Except.ok x => x == v
  | Except.error _ => false

/-- Boolean check: `e` is `Except.error msg`. -/
def isErrorWith (e : Except String Nat) (msg : String) : Bool :=
  match e with
  | Except.ok _ => false
  | Except.error m => m == msg

/-- Boolean check: `e` is some `Except.error`. -/
def isError (e : Except String Nat) : Bool :=
  match e with
  | Except.ok _ => false
  | Except.error _ => true

-- ### Unit tests for `prog`

example : isOkWith (prog 3) 6 = true := by native_decide
example : isOkWith (prog 0) 1 = true := by native_decide
example : isErrorWith (prog (-1)) "Input must be a non-negative integer (got n=-1)" = true := by
  native_decide

#eval prog 5    -- Except.ok 120
#eval prog (-1) -- Except.error "Input must be a non-negative integer (got n=-1)"

/-! ## Properties -/

/-- Recurrence property: `(n+1)! = (n+1) * n!`. -/
def factorial_succ_prop (n : Nat) : Prop := myFactorial (n + 1) = (n + 1) * myFactorial n

theorem factorial_succ_thm (n : Nat) : factorial_succ_prop n := rfl

/-- Positivity property: `n! > 0`. -/
def factorial_pos_prop (n : Nat) : Prop := 0 < myFactorial n

theorem factorial_pos_thm (n : Nat) : factorial_pos_prop n := by
  induction n with
  | zero => exact Nat.one_pos
  | succ k ih => exact Nat.mul_pos (Nat.succ_pos k) ih

/-- Monotonicity property: factorial is monotone on `Nat`. -/
def factorial_mono_prop (m n : Nat) : Prop := m ≤ n → myFactorial m ≤ myFactorial n

theorem factorial_mono_thm (m n : Nat) : factorial_mono_prop m n := by
  intro h
  induction h with
  | refl => exact le_refl _
  | step hh ih =>
      rename_i k
      have hstep : myFactorial k ≤ myFactorial (k + 1) := by
        have h1 : (1 : Nat) ≤ k + 1 := Nat.succ_pos k
        calc myFactorial k = 1 * myFactorial k := (one_mul _).symm
          _ ≤ (k + 1) * myFactorial k := mul_le_mul_right' h1 _
          _ = myFactorial (k + 1) := rfl
      exact le_trans ih hstep

/-- On admissible inputs `prog` returns `ok n!`. -/
def prog_ok_prop (n : Int) : Prop := 0 ≤ n → prog n = Except.ok (myFactorial n.toNat)

theorem prog_ok_thm (n : Int) : prog_ok_prop n := by
  intro h
  unfold prog
  rw [if_pos h]

/-- On negative inputs `prog` raises a `ValueError` (modelled as `Except.error`). -/
def prog_error_prop (n : Int) : Prop := n < 0 → ∃ msg : String, prog n = Except.error msg

theorem prog_error_thm (n : Int) : prog_error_prop n := by
  intro h
  exact ⟨s!"Input must be a non-negative integer (got n={n})",
    by unfold prog; rw [if_neg (not_le_of_gt h)]⟩

/-! ## Post-condition -/

/-- Post-condition: conjunction of the properties, relating input and output. -/
def Post_prop (n : Int) : Prop :=
  factorial_pos_prop n.toNat ∧
  factorial_succ_prop n.toNat ∧
  (∀ m : Nat, factorial_mono_prop m n.toNat) ∧
  prog n = Except.ok (myFactorial n.toNat)

/-! ## Property-based tests -/

-- Randomized PBT: positivity.
#eval Plausible.Testable.check (∀ n : Nat, 0 < myFactorial n)

-- Randomized PBT: the recurrence.
#eval Plausible.Testable.check (∀ n : Nat, myFactorial (n + 1) = (n + 1) * myFactorial n)

-- Randomized PBT: monotonicity (decidable implication restricted to admissible inputs).
#eval Plausible.Testable.check (∀ m n : Nat, m ≤ n → myFactorial m ≤ myFactorial n)

-- Bounded PBT: positivity (exhaustive small cases).
example : (List.range 25).all (fun n => decide (0 < myFactorial n)) = true := by native_decide

-- Bounded PBT: the recurrence.
example : (List.range 25).all (fun n =>
    decide (myFactorial (n + 1) = (n + 1) * myFactorial n)) = true := by native_decide

-- Bounded PBT: monotonicity.
example : (List.range 15).all (fun m =>
    (List.range 15).all (fun n =>
      !(decide (m ≤ n)) || decide (myFactorial m ≤ myFactorial n))) = true := by
  native_decide

-- Bounded PBT: `prog` returns `ok` on non-negative inputs.
example : (List.range 12).all (fun k =>
    isOkWith (prog (k : Int)) (myFactorial k)) = true := by native_decide

-- Bounded PBT: `prog` raises `ValueError` on negative inputs.
example : (List.range 12).all (fun k => isError (prog (-(k : Int) - 1))) = true := by
  native_decide

/-- Executable Boolean form of the post-condition on admissible inputs. -/
def postCheck (n : Nat) : Bool :=
  decide (0 < myFactorial n) &&
  decide (myFactorial (n + 1) = (n + 1) * myFactorial n) &&
  (List.range (n + 1)).all (fun m => decide (myFactorial m ≤ myFactorial n)) &&
  isOkWith (prog (n : Int)) (myFactorial n)

-- Bounded PBT: the post-condition.
example : (List.range 12).all (fun n => postCheck n) = true := by native_decide

/-! ## Correctness theorem: `Pre → Post` -/

theorem correctness (n : Int) (h : Pre n) : Post_prop n :=
  ⟨factorial_pos_thm n.toNat, factorial_succ_thm n.toNat,
    fun m hm => factorial_mono_thm m n.toNat hm, prog_ok_thm n h⟩

/-! ## Imperative implementation -/

/-- Imperative factorial using `Id.run` with mutable state. -/
def myFactorialImp (n : Nat) : Nat := Id.run do
  let mut result := 1
  for i in List.range n do
    result := result * (i + 1)
  return result

-- ### Imperative tests

example : myFactorialImp 0 = 1 := by native_decide
example : myFactorialImp 3 = 6 := by native_decide
example : myFactorialImp 5 = 120 := by native_decide

#eval myFactorialImp 0  -- 1
#eval myFactorialImp 5  -- 120

/-! ## Equivalence of the functional and imperative implementations -/

/-- The `Id.run` loop with mutable state, as a named function. -/
def loopRun (xs : List Nat) (acc : Nat) : Nat := Id.run do
  let mut result := acc
  for i in xs do
    result := result * (i + 1)
  return result

/-- The `Id.run` loop is a left fold over the list. -/
theorem loopRun_foldl (xs : List Nat) (acc : Nat) :
    loopRun xs acc = xs.foldl (fun r i => r * (i + 1)) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      rw [List.foldl_cons, ← ih]
      simp only [loopRun, List.forIn_cons]
      rfl

/-- Folding multiplication over `range n` computes a multiple of `n!`. -/
theorem foldl_factorial (n : Nat) (acc : Nat) :
    (List.range n).foldl (fun r i => r * (i + 1)) acc = acc * myFactorial n := by
  induction n generalizing acc with
  | zero => show acc = acc * 1; rw [mul_one]
  | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
      show acc * myFactorial k * (k + 1) = acc * ((k + 1) * myFactorial k)
      ring

theorem myFactorialImp_eq_myFactorial (n : Nat) : myFactorialImp n = myFactorial n := by
  have h : myFactorialImp n = (List.range n).foldl (fun r i => r * (i + 1)) 1 :=
    loopRun_foldl (List.range n) 1
  rw [h, foldl_factorial, one_mul]

end «16_MyFactorial»
