import Mathlib

/-!
# 16_MyFactorial

Lean 4 formalization of a Python factorial program.

Python source semantics:
* `pre(n)` holds iff `n` is an integer and `n >= 0`.
* `prog(n)` returns `n!` for a non-negative integer, with the edge cases
  `factorial(0) = 1` and `factorial(1) = 1`.
* Otherwise `prog` raises `ValueError` (negative integers, and non-integers
  such as `3.14`).

The successful path is the iterative product `1 * 2 * ... * n` (empty product `1`
when `n = 0`). Non-integer inputs are represented by `PyInput.nonInteger`,
which is the Lean counterpart of failing `isinstance(n, int)`. Failure is
represented by `Option.none` (the analogue of `ValueError`).
-/

namespace «16_MyFactorial»

/-!
## Implementation

Functional translation of the Python loop:
`result = 1; for i in range(1, n + 1): result *= i`.
-/

/-- Product `1 * 2 * ... * n`, with the empty product `factorial 0 = 1`. -/
def factorial (n : Nat) : Nat :=
  (List.range' 1 n).foldl (fun acc i => acc * i) 1

/-- Partial factorial accumulator: multiplying `k!` by the next `n` integers. -/
lemma foldl_range'_factorial (k n : Nat) :
    (List.range' (k + 1) n).foldl (fun acc i => acc * i) (Nat.factorial k)
      = Nat.factorial (k + n) := by
  induction n generalizing k with
  | zero => simp [List.range']
  | succ n ih =>
    rw [List.range'_succ, List.foldl_cons]
    have hacc : Nat.factorial k * (k + 1) = Nat.factorial (k + 1) := by
      rw [Nat.factorial_succ, Nat.mul_comm]
    rw [hacc]
    rw [show k + (n + 1) = k + 1 + n by omega]
    exact ih (k + 1)

/-- The functional implementation agrees with Mathlib's `Nat.factorial`. -/
lemma factorial_eq_std (n : Nat) : factorial n = n.factorial := by
  have h := foldl_range'_factorial 0 n
  simpa [factorial, Nat.factorial_zero, Nat.zero_add] using h

/-- `foldl (· * ·) acc = acc * prod`, the algebraic content of the loop. -/
lemma foldl_mul_prod (acc : Nat) (xs : List Nat) :
    xs.foldl (fun a b => a * b) acc = acc * xs.prod := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.prod_cons, ih]
    rw [Nat.mul_assoc]

/-- Values that can reach the Python function: integers, or a non-integer
(such as the test input `3.14`). -/
inductive PyInput where
  | ofInt (n : Int)
  | nonInteger
  deriving DecidableEq, Repr, BEq

/-- Boolean precondition, matching Python `pre`. -/
def pre (x : PyInput) : Bool :=
  match x with
  | .ofInt n => if n >= 0 then true else false
  | .nonInteger => false

/-- Python `prog` on the modelled inputs. `none` means `ValueError`. -/
def prog (x : PyInput) : Option Nat :=
  match x with
  | .nonInteger => none
  | .ofInt n =>
    if n < 0 then
      none
    else
      some (factorial n.toNat)

/-- Integer entry point used by the Python tests (`prog(3)`, `prog(-1)`, ...). -/
def progInt (n : Int) : Option Nat :=
  prog (.ofInt n)


/-!
## Unit tests
-/

/-- Python basic unit test: `prog(3) == 6`. -/
example : progInt 3 = some 6 := by native_decide
#eval progInt 3

/-- Python edge unit test: `prog(0) == 1`. -/
example : progInt 0 = some 1 := by native_decide
#eval progInt 0

/-- Edge: `factorial(1) = 1`. -/
example : progInt 1 = some 1 := by native_decide
#eval progInt 1

example : factorial 2 = 2 := by native_decide
#eval factorial 2

example : factorial 4 = 24 := by native_decide
#eval factorial 4

example : factorial 5 = 120 := by native_decide
#eval factorial 5

example : factorial 6 = 720 := by native_decide
#eval factorial 6

example : factorial 10 = 3628800 := by native_decide
#eval factorial 10

/-- Python negative test: `prog(-1)` raises `ValueError`. -/
example : progInt (-1) = none := by native_decide
#eval progInt (-1)

/-- Python negative test: non-integer input (e.g. `3.14`) raises `ValueError`. -/
example : prog .nonInteger = none := by native_decide
#eval prog .nonInteger

example : pre (.ofInt 3) = true := by native_decide
example : pre (.ofInt 0) = true := by native_decide
example : pre (.ofInt (-1)) = false := by native_decide
example : pre .nonInteger = false := by native_decide

/-!
## Pre-condition
-/

/-- **Pre-condition.** The input is a non-negative integer.

This is the propositional form of Python `pre`: `isinstance(n, int) and n >= 0`.
`PyInput.nonInteger` encodes inputs that fail the `isinstance` check. -/
def Pre (x : PyInput) : Prop :=
  match x with
  | .ofInt n => 0 <= n
  | .nonInteger => False

/-- `Pre` is exactly the Boolean `pre` predicate. -/
theorem Pre_iff_pre (x : PyInput) : Pre x <-> pre x = true := by
  cases x with
  | nonInteger => simp [Pre, pre]
  | ofInt n =>
    by_cases h : 0 <= n
    . simp [Pre, pre, h]
    . simp [Pre, pre, h]

/-!
## Property propositions and theorems
-/

/-- **Zero property**: `factorial(0) = 1` by definition. -/
def factorial_zero_prop : Prop := factorial 0 = 1

theorem factorial_zero_thm : factorial_zero_prop := by
  rw [factorial_zero_prop, factorial_eq_std]
  rfl

/-- **One property**: `factorial(1) = 1`. -/
def factorial_one_prop : Prop := factorial 1 = 1

theorem factorial_one_thm : factorial_one_prop := by
  rw [factorial_one_prop, factorial_eq_std]
  rfl

/-- **Recurrence property**: `(n + 1)! = n! * (n + 1)`, matching the loop step. -/
def factorial_recurrence_prop (n : Nat) : Prop :=
  factorial (n + 1) = factorial n * (n + 1)

theorem factorial_recurrence_thm (n : Nat) : factorial_recurrence_prop n := by
  rw [factorial_recurrence_prop, factorial_eq_std, factorial_eq_std, Nat.factorial_succ,
    Nat.mul_comm]

/-- **Positivity property**: `0 < n!` for every natural `n`. -/
def factorial_pos_prop (n : Nat) : Prop := 0 < factorial n

theorem factorial_pos_thm (n : Nat) : factorial_pos_prop n := by
  rw [factorial_pos_prop, factorial_eq_std]
  exact Nat.factorial_pos n

/-- **Self-lower-bound property**: `n <= n!`. -/
def factorial_self_le_prop (n : Nat) : Prop := n <= factorial n

theorem factorial_self_le_thm (n : Nat) : factorial_self_le_prop n := by
  rw [factorial_self_le_prop, factorial_eq_std]
  exact Nat.self_le_factorial n

/-- **Monotonicity property**: `m <= n` implies `m! <= n!`. -/
def factorial_mono_prop (m n : Nat) : Prop :=
  m <= n -> factorial m <= factorial n

theorem factorial_mono_thm (m n : Nat) : factorial_mono_prop m n := by
  intro h
  rw [factorial_eq_std, factorial_eq_std]
  exact Nat.factorial_le h

/-- **Divisibility property**: `m <= n` implies `m! | n!`. -/
def factorial_dvd_prop (m n : Nat) : Prop :=
  m <= n -> factorial m ∣ factorial n

theorem factorial_dvd_thm (m n : Nat) : factorial_dvd_prop m n := by
  intro h
  rw [factorial_eq_std, factorial_eq_std]
  exact Nat.factorial_dvd_factorial h

/-- **Standard-factorial property**: the implementation equals `Nat.factorial`. -/
def factorial_eq_std_prop (n : Nat) : Prop := factorial n = n.factorial

theorem factorial_eq_std_thm (n : Nat) : factorial_eq_std_prop n :=
  factorial_eq_std n

/-- **Product property**: `n!` is the product of `List.range' 1 n`. -/
def factorial_prod_prop (n : Nat) : Prop :=
  factorial n = (List.range' 1 n).prod

theorem factorial_prod_thm (n : Nat) : factorial_prod_prop n := by
  rw [factorial_prod_prop, factorial]
  have h := foldl_mul_prod 1 (List.range' 1 n)
  simpa using h


/-- **Success property**: a non-negative integer input returns `n!`. -/
def prog_success_prop (n : Int) : Prop :=
  0 <= n -> progInt n = some (factorial n.toNat)

theorem prog_success_thm (n : Int) : prog_success_prop n := by
  intro h
  have hlt : Not (n < 0) := not_lt.mpr h
  simp [progInt, prog, hlt]

/-- **Negative-error property**: a negative integer raises (returns `none`). -/
def prog_error_neg_prop (n : Int) : Prop :=
  n < 0 -> progInt n = none

theorem prog_error_neg_thm (n : Int) : prog_error_neg_prop n := by
  intro h
  simp [progInt, prog, h]

/-- **Non-integer-error property**: a non-integer (e.g. `3.14`) raises. -/
def prog_error_nonint_prop : Prop := prog .nonInteger = none

theorem prog_error_nonint_thm : prog_error_nonint_prop := by
  simp [prog_error_nonint_prop, prog]

/-- **Pre/success equivalence**: `prog` returns a value iff the precondition holds. -/
def prog_defined_iff_pre_prop (x : PyInput) : Prop :=
  (Exists (fun v => prog x = some v)) <-> Pre x

theorem prog_defined_iff_pre_thm (x : PyInput) : prog_defined_iff_pre_prop x := by
  cases x with
  | nonInteger =>
    simp [prog_defined_iff_pre_prop, prog, Pre]
  | ofInt n =>
    by_cases h : 0 <= n
    . have hlt : Not (n < 0) := not_lt.mpr h
      simp [prog_defined_iff_pre_prop, prog, Pre, h, hlt]
    . have hlt : n < 0 := lt_of_not_ge h
      simp [prog_defined_iff_pre_prop, prog, Pre, h, hlt]

/-- **Boolean pre on negatives**. -/
def pre_neg_prop (n : Int) : Prop := n < 0 -> pre (.ofInt n) = false

theorem pre_neg_thm (n : Int) : pre_neg_prop n := by
  intro h
  have hle : Not (0 <= n) := not_le.mpr h
  simp [pre, hle]

/-- **Boolean pre on non-integers**. -/
def pre_nonint_prop : Prop := pre .nonInteger = false

theorem pre_nonint_thm : pre_nonint_prop := by
  simp [pre_nonint_prop, pre]

/-- **Boolean pre on non-negative integers**. -/
def pre_nonneg_prop (n : Int) : Prop := 0 <= n -> pre (.ofInt n) = true

theorem pre_nonneg_thm (n : Int) : pre_nonneg_prop n := by
  intro h
  simp [pre, h]

/-!
## Post-condition

Conjunction of the specification for this input and the factorial laws.
-/

/-- Natural number carried by an integer input; unused on the error branch. -/
def inputToNat (x : PyInput) : Nat :=
  match x with
  | .ofInt n => n.toNat
  | .nonInteger => 0

/-- Specification of `prog` on one input: success with `n!` exactly when `Pre` holds. -/
def prog_spec_prop (x : PyInput) : Prop :=
  (Pre x ->
    prog x = some (factorial (inputToNat x)) /\
    prog x = some (inputToNat x).factorial) /\
  ((Not (Pre x)) -> prog x = none)

/-- **Post-condition**: input specification conjoined with the factorial properties. -/
def Post_prop (x : PyInput) : Prop :=
  prog_spec_prop x /\
  factorial_zero_prop /\
  factorial_one_prop /\
  (forall n, factorial_recurrence_prop n) /\
  (forall n, factorial_pos_prop n) /\
  (forall n, factorial_self_le_prop n) /\
  (forall m n, factorial_mono_prop m n) /\
  (forall m n, factorial_dvd_prop m n) /\
  (forall n, factorial_eq_std_prop n) /\
  (forall n, factorial_prod_prop n) /\
  prog_error_nonint_prop /\
  (forall n, prog_success_prop n) /\
  (forall n, prog_error_neg_prop n) /\
  (forall y, prog_defined_iff_pre_prop y) /\
  (forall n, pre_neg_prop n) /\
  pre_nonint_prop /\
  (forall n, pre_nonneg_prop n)


/-!
## Property-based tests

Executable checks for every stated property and for the post-condition.
Randomized tests use Plausible; bounded tests exhaust small inputs (including
precondition-restricted properties, so a Plausible "Gave up" cannot hide a bug).
-/

-- PBT: factorial_zero_prop
example : factorial 0 == 1 := by native_decide

-- PBT: factorial_one_prop
example : factorial 1 == 1 := by native_decide

-- PBT: factorial_recurrence_prop
#eval Plausible.Testable.check (forall n : Nat, factorial (n + 1) = factorial n * (n + 1))
example : (List.range 20).all (fun n => factorial (n + 1) == factorial n * (n + 1)) = true := by
  native_decide

-- PBT: factorial_pos_prop
#eval Plausible.Testable.check (forall n : Nat, 0 < factorial n)
example : (List.range 20).all (fun n => decide (0 < factorial n)) = true := by native_decide

-- PBT: factorial_self_le_prop
#eval Plausible.Testable.check (forall n : Nat, n <= factorial n)
example : (List.range 20).all (fun n => decide (n <= factorial n)) = true := by native_decide

-- PBT: factorial_mono_prop
#eval Plausible.Testable.check (forall m n : Nat, m <= n -> factorial m <= factorial n)
example : (List.range 12).all (fun m =>
    (List.range 12).all (fun n => decide (m <= n -> factorial m <= factorial n))) = true := by
  native_decide

-- PBT: factorial_dvd_prop
#eval Plausible.Testable.check (forall m n : Nat, m <= n -> factorial m ∣ factorial n)
example : (List.range 12).all (fun m =>
    (List.range 12).all (fun n => decide (m <= n -> factorial m ∣ factorial n))) = true := by
  native_decide

-- PBT: factorial_eq_std_prop
#eval Plausible.Testable.check (forall n : Nat, factorial n = n.factorial)
example : (List.range 20).all (fun n => factorial n == n.factorial) = true := by native_decide

-- PBT: factorial_prod_prop
#eval Plausible.Testable.check (forall n : Nat, factorial n = (List.range' 1 n).prod)
example : (List.range 20).all (fun n => factorial n == (List.range' 1 n).prod) = true := by
  native_decide

-- PBT: prog_success_prop
#eval Plausible.Testable.check (forall n : Int, 0 <= n -> progInt n = some (factorial n.toNat))
example : (List.range 20).all (fun n => progInt (n : Int) == some (factorial n)) = true := by
  native_decide

-- PBT: prog_error_neg_prop (bounded, because random Int samples often miss `n < 0`)
#eval Plausible.Testable.check (forall n : Nat, progInt (-(n : Int) - 1) = none)
example : (List.range 30).all (fun i => progInt (-(i : Int) - 1) == none) = true := by
  native_decide

-- PBT: prog_error_nonint_prop
example : prog .nonInteger == none := by native_decide

-- PBT: prog_defined_iff_pre_prop
example :
    (List.range 21).all (fun i =>
      let n : Int := (i : Int) - 10
      (progInt n).isSome == decide (0 <= n)) = true := by
  native_decide
example : (prog .nonInteger).isSome = false := by native_decide

-- PBT: pre_neg_prop / pre_nonneg_prop / pre_nonint_prop
example : (List.range 30).all (fun i => pre (.ofInt (-(i : Int) - 1)) == false) = true := by
  native_decide
example : (List.range 20).all (fun i => pre (.ofInt (i : Int)) == true) = true := by
  native_decide
example : pre .nonInteger == false := by native_decide

-- PBT: Post_prop executable content on small integers and the non-integer input
example : (List.range 15).all (fun i =>
    let n : Int := (i : Int) - 5
    match progInt n with
    | some v =>
      decide (0 <= n) && v == n.toNat.factorial && v == factorial n.toNat &&
        decide (0 < v) && decide (n.toNat <= v)
    | none => decide (n < 0)) = true := by
  native_decide
example : prog .nonInteger = none := by native_decide
example : (List.range 15).all (fun n =>
    factorial n == n.factorial && factorial (n + 1) == factorial n * (n + 1) &&
      decide (0 < factorial n) && decide (n <= factorial n)) = true := by
  native_decide

/-!
## Correctness theorem
-/

theorem prog_spec_thm (x : PyInput) : prog_spec_prop x := by
  cases x with
  | nonInteger =>
    simp [prog_spec_prop, Pre, prog]
  | ofInt n =>
    by_cases h : 0 <= n
    . have hlt : Not (n < 0) := not_lt.mpr h
      simp [prog_spec_prop, Pre, prog, inputToNat, h, hlt, factorial_eq_std]
    . have hlt : n < 0 := lt_of_not_ge h
      simp [prog_spec_prop, Pre, prog, h, hlt]

/-- Full post-condition, including inputs that violate `Pre`. -/
theorem post_thm (x : PyInput) : Post_prop x :=
  ⟨prog_spec_thm x,
   factorial_zero_thm,
   factorial_one_thm,
   factorial_recurrence_thm,
   factorial_pos_thm,
   factorial_self_le_thm,
   factorial_mono_thm,
   factorial_dvd_thm,
   factorial_eq_std_thm,
   factorial_prod_thm,
   prog_error_nonint_thm,
   prog_success_thm,
   prog_error_neg_thm,
   prog_defined_iff_pre_thm,
   pre_neg_thm,
   pre_nonint_thm,
   pre_nonneg_thm⟩

/-- **Correctness**: if the precondition holds, the post-condition holds. -/
theorem correctness_thm (x : PyInput) (_hPre : Pre x) : Post_prop x :=
  post_thm x


/-!
## Imperative implementation

Direct translation of the Python loop, using mutable state inside `Id.run`.
The `n == 0` early return matches the Python source; it is redundant with the
empty loop and is proved equivalent below.
-/

def factorialImp (n : Nat) : Nat :=
  Id.run do
    if n == 0 then
      return 1
    let mut result : Nat := 1
    for i in List.range' 1 n do
      result := result * i
    return result

/-- Imperative `prog`: reject precondition failures, otherwise run the loop. -/
def progImp (x : PyInput) : Option Nat :=
  Id.run do
    match x with
    | .nonInteger =>
      return none
    | .ofInt n =>
      if n < 0 then
        return none
      return some (factorialImp n.toNat)

def progIntImp (n : Int) : Option Nat :=
  progImp (.ofInt n)

/-!
## Imperative tests
-/

example : factorialImp 0 = 1 := by native_decide
#eval factorialImp 0

example : factorialImp 1 = 1 := by native_decide
#eval factorialImp 1

example : factorialImp 3 = 6 := by native_decide
#eval factorialImp 3

example : factorialImp 5 = 120 := by native_decide
#eval factorialImp 5

example : factorialImp 7 = 5040 := by native_decide
#eval factorialImp 7

example : progIntImp 3 = some 6 := by native_decide
#eval progIntImp 3

example : progIntImp 0 = some 1 := by native_decide
#eval progIntImp 0

example : progIntImp (-1) = none := by native_decide
#eval progIntImp (-1)

example : progImp .nonInteger = none := by native_decide
#eval progImp .nonInteger

/-!
## Equivalence theorem
-/

/-- The imperative loop agrees with the functional product. -/
theorem factorial_eq_imp (n : Nat) : factorial n = factorialImp n := by
  cases n with
  | zero =>
    simp [factorial, factorialImp, List.range']
  | succ n =>
    simp [factorial, factorialImp]

/-- **Equivalence**: functional `prog` and imperative `progImp` agree on every input. -/
theorem equivalence_thm (x : PyInput) : prog x = progImp x := by
  cases x with
  | nonInteger =>
    simp [prog, progImp]
  | ofInt n =>
    by_cases h : n < 0
    . simp [prog, progImp, h]
    . simp [prog, progImp, h, factorial_eq_imp]

/-- Equivalence on the integer entry point used by the Python tests. -/
theorem equivalence_int_thm (n : Int) : progInt n = progIntImp n := by
  simpa [progInt, progIntImp] using equivalence_thm (.ofInt n)

/-- Equivalence of the two Nat implementations. -/
theorem factorial_equivalence_thm (n : Nat) : factorial n = factorialImp n :=
  factorial_eq_imp n

-- PBT: equivalence
#eval Plausible.Testable.check (forall n : Nat, factorial n = factorialImp n)
example : (List.range 20).all (fun n => factorial n == factorialImp n) = true := by
  native_decide
example : (List.range 15).all (fun i =>
    let n : Int := (i : Int) - 5
    progInt n == progIntImp n) = true := by
  native_decide
example : prog .nonInteger == progImp .nonInteger := by native_decide

end «16_MyFactorial»
