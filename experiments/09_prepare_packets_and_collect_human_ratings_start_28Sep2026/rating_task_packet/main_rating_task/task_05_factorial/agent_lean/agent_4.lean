import Mathlib
import Plausible

/-!
# 16_MyFactorial

Lean 4 formalization of a Python factorial program.

The Python function returns `n!` for a non-negative integer `n`
(`0! = 1` by definition) and raises `ValueError` otherwise.
The rejected inputs in the Python tests are negative integers and
non-integers such as `3.14`.

Those inputs are modelled by `Input`: an `Int`, or a `Float` standing
for a non-integer. `Except.error` models `ValueError`. The message uses
the Python template `Input must be a non-negative integer (got n=...)`.
Lean's `Float.toString` prints `3.14` as `3.140000`, so that payload
differs from CPython's rendering; the rejection itself does not.

The mathematical implementation multiplies `1 .. n` (the empty product
is `1`). The imperative implementation follows the Python control flow:
reject a violated precondition, return `1` when `n = 0`, otherwise
accumulate `result *= i` for `i` in `1 .. n`.
-/

namespace «16_MyFactorial»

/-- A value the Python function may receive.

`3.14` in the Python tests is a `float`, so non-integers are represented
by `Input.float`. Integers, including negatives, are `Input.int`. -/
inductive Input
  | int (n : Int)
  | float (x : Float)
  deriving Repr

/-- `Except String Nat` has decidable equality, so concrete runs can be
compared by `native_decide` and by property-based tests. -/
instance : DecidableEq (Except String Nat) := fun a b =>
  match a, b with
  | .ok x, .ok y =>
    decidable_of_iff (x = y) <| by
      constructor
      · intro h; cases h; rfl
      · intro h; cases h; rfl
  | .error s, .error t =>
    decidable_of_iff (s = t) <| by
      constructor
      · intro h; cases h; rfl
      · intro h; cases h; rfl
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

/-- Python `f"Input must be a non-negative integer (got n={shown})"`. -/
def errMsg (shown : String) : String :=
  "Input must be a non-negative integer (got n=" ++ shown ++ ")"

/-- Factorial of a natural number.

This is the product `1 * 2 * ... * n`, i.e. the body of the Python loop
`for i in range(1, n + 1): result *= i` starting from `result = 1`.
The empty product gives `factorial 0 = 1`. -/
def factorial (n : Nat) : Nat :=
  (List.range' 1 n).foldl (· * ·) 1

/-- Functional program: `n!` on a non-negative integer, otherwise the
`ValueError` message. -/
def prog (x : Input) : Except String Nat :=
  match x with
  | .int n =>
    if 0 ≤ n then
      .ok (factorial n.toNat)
    else
      .error (errMsg (toString n))
  | .float y =>
    .error (errMsg (toString y))

/-! ## Unit tests -/

example : factorial 0 = 1 := by native_decide

example : factorial 1 = 1 := by native_decide

example : factorial 3 = 6 := by native_decide

example : factorial 5 = 120 := by native_decide

example : factorial 10 = 3628800 := by native_decide

example : prog (.int 3) = .ok 6 := by native_decide

example : prog (.int 0) = .ok 1 := by native_decide

example : prog (.int 1) = .ok 1 := by native_decide

example : prog (.int 5) = .ok 120 := by native_decide

example : prog (.int (-1)) = .error (errMsg (toString (-1 : Int))) := by native_decide

example : prog (.float (3.14 : Float)) = .error (errMsg (toString (3.14 : Float))) := by
  native_decide

#eval factorial 0

#eval factorial 3

#eval factorial 7

#eval prog (.int 3)

#eval prog (.int 0)

#eval prog (.int (-1))

#eval prog (.float (3.14 : Float))

/-! ## Precondition -/

/-- Python `pre`: `True` iff the input is a non-negative integer.

`isinstance(n, int) and n >= 0`. Floats fail `isinstance(..., int)`. -/
def pre (x : Input) : Bool :=
  match x with
  | .int n => decide (0 ≤ n)
  | .float _ => false

/-- Precondition as a proposition. -/
def Pre (x : Input) : Prop :=
  pre x = true

instance (x : Input) : Decidable (Pre x) :=
  decidable_of_iff (pre x = true) Iff.rfl

/-! ## Properties -/

/-- `0! = 1`, the Python base case. -/
def factorial_zero_prop : Prop :=
  factorial 0 = 1

theorem factorial_zero_thm : factorial_zero_prop := by
  simp [factorial_zero_prop, factorial]

/-- Recurrence implemented by the loop: `(n + 1)! = n! * (n + 1)`. -/
def factorial_succ_prop : Prop :=
  ∀ n : Nat, factorial (n + 1) = factorial n * (n + 1)

theorem factorial_succ_thm : factorial_succ_prop := by
  intro n
  unfold factorial
  rw [List.range'_1_concat, List.foldl_append]
  simp [Nat.add_comm]

/-- `1! = 1`. -/
def factorial_one_prop : Prop :=
  factorial 1 = 1

theorem factorial_one_thm : factorial_one_prop := by
  simpa [factorial_one_prop, factorial_zero_thm] using factorial_succ_thm 0

/-- The implementation agrees with Mathlib's factorial. -/
def factorial_eq_mathlib_prop : Prop :=
  ∀ n : Nat, factorial n = Nat.factorial n

theorem factorial_eq_mathlib_thm : factorial_eq_mathlib_prop := by
  intro n
  induction n with
  | zero =>
    rw [factorial_zero_thm, Nat.factorial_zero]
  | succ n ih =>
    rw [factorial_succ_thm, ih, Nat.factorial_succ, Nat.mul_comm]

/-- Every factorial is strictly positive. -/
def factorial_pos_prop : Prop :=
  ∀ n : Nat, 0 < factorial n

theorem factorial_pos_thm : factorial_pos_prop := by
  intro n
  rw [factorial_eq_mathlib_thm]
  exact Nat.factorial_pos n

/-- Factorial is monotone. -/
def factorial_mono_prop : Prop :=
  ∀ m n : Nat, m ≤ n → factorial m ≤ factorial n

theorem factorial_mono_thm : factorial_mono_prop := by
  intro m n h
  rw [factorial_eq_mathlib_thm m, factorial_eq_mathlib_thm n]
  exact Nat.factorial_le h

/-- For `n ≥ 1`, factorial grows strictly at the next integer. -/
def factorial_strict_succ_prop : Prop :=
  ∀ n : Nat, 1 ≤ n → factorial n < factorial (n + 1)

theorem factorial_strict_succ_thm : factorial_strict_succ_prop := by
  intro n hn
  rw [factorial_succ_thm]
  exact (Nat.lt_mul_iff_one_lt_right (factorial_pos_thm n)).mpr (Nat.lt_succ_of_le hn)

/-- `n ≤ n!`. -/
def factorial_self_le_prop : Prop :=
  ∀ n : Nat, n ≤ factorial n

theorem factorial_self_le_thm : factorial_self_le_prop := by
  intro n
  rw [factorial_eq_mathlib_thm]
  exact Nat.self_le_factorial n

/-- `n! = 1` exactly for `n = 0` and `n = 1`. -/
def factorial_eq_one_prop : Prop :=
  ∀ n : Nat, factorial n = 1 ↔ n ≤ 1

theorem factorial_eq_one_thm : factorial_eq_one_prop := by
  intro n
  rw [factorial_eq_mathlib_thm]
  exact Nat.factorial_eq_one

/-- The loop product is the product of the integers from `1` through `n`. -/
def factorial_prod_prop : Prop :=
  ∀ n : Nat, factorial n = Finset.prod (Finset.Icc 1 n) id

theorem factorial_prod_thm : factorial_prod_prop := by
  intro n
  induction n with
  | zero =>
    rw [factorial_zero_thm]
    simp [Finset.prod_empty]
  | succ n ih =>
    rw [factorial_succ_thm, ih, Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]
    simp [id]

/-- A natural number is accepted and the result is its factorial. -/
def prog_nat_prop : Prop :=
  ∀ n : Nat, prog (.int (n : Int)) = .ok (factorial n)

theorem prog_nat_thm : prog_nat_prop := by
  intro n
  simp [prog, Int.toNat_natCast]

/-- A negative integer raises `ValueError` with the Python message. -/
def prog_neg_prop : Prop :=
  ∀ n : Int, n < 0 → prog (.int n) = .error (errMsg (toString n))

theorem prog_neg_thm : prog_neg_prop := by
  intro n hn
  have hnot : ¬ 0 ≤ n := (Int.not_le).mpr hn
  simp [prog, hnot]

/-- Every non-integer float raises `ValueError` with the Python message. -/
def prog_float_prop : Prop :=
  ∀ y : Float, prog (.float y) = .error (errMsg (toString y))

theorem prog_float_thm : prog_float_prop := by
  intro y
  simp [prog]

/-- `Pre` holds exactly on the natural numbers, embedded as integers. -/
def pre_iff_nat_prop : Prop :=
  ∀ x : Input, Pre x ↔ ∃ n : Nat, x = .int (n : Int)

theorem pre_iff_nat_thm : pre_iff_nat_prop := by
  intro x
  cases x with
  | float _ =>
    simp [Pre, pre]
  | int n =>
    constructor
    · intro h
      have h0 : 0 ≤ n := by
        unfold Pre pre at h
        simpa using h
      refine ⟨n.toNat, ?_⟩
      apply congrArg Input.int
      exact (Int.toNat_of_nonneg h0).symm
    · rintro ⟨k, hk⟩
      have hn : n = (k : Int) := by
        injection hk
      unfold Pre pre
      simp [hn]

/-- On a valid input the returned value is that input's factorial. -/
def result_prop (x : Input) (r : Except String Nat) : Prop :=
  Pre x → ∃ n : Nat, x = .int (n : Int) ∧ r = .ok (factorial n) ∧ 0 < factorial n

/-- Post-condition: the factorial laws, the precondition partition, and
the success specification for this particular input and result. -/
def Post_prop (x : Input) (r : Except String Nat) : Prop :=
  factorial_zero_prop ∧
  factorial_one_prop ∧
  factorial_succ_prop ∧
  factorial_pos_prop ∧
  factorial_mono_prop ∧
  factorial_strict_succ_prop ∧
  factorial_self_le_prop ∧
  factorial_eq_mathlib_prop ∧
  factorial_eq_one_prop ∧
  factorial_prod_prop ∧
  prog_nat_prop ∧
  prog_neg_prop ∧
  prog_float_prop ∧
  pre_iff_nat_prop ∧
  result_prop x r

/-! ## Property-based tests

Each test is an executable Boolean check of the corresponding `_prop`
(or of `Post_prop`). A passing check is evidence, not a proof.
-/

-- PBT: factorial_zero_prop
example : (factorial 0 == 1) = true := by native_decide

-- PBT: factorial_one_prop
example : (factorial 1 == 1) = true := by native_decide

-- PBT: factorial_succ_prop
#eval Plausible.Testable.check
  (∀ n : Nat, factorial (n + 1) = factorial n * (n + 1))

example : (List.range 25).all (fun n => factorial (n + 1) == factorial n * (n + 1)) = true := by
  native_decide

-- PBT: factorial_pos_prop
#eval Plausible.Testable.check (∀ n : Nat, 0 < factorial n)

example : (List.range 30).all (fun n => decide (0 < factorial n)) = true := by
  native_decide

-- PBT: factorial_mono_prop
#eval Plausible.Testable.check (∀ m n : Nat, m ≤ n → factorial m ≤ factorial n)

example :
    (List.range 12).all (fun m =>
      (List.range 12).all (fun n =>
        if m ≤ n then decide (factorial m ≤ factorial n) else true)) = true := by
  native_decide

-- PBT: factorial_strict_succ_prop
-- Quantifying over `n + 1` keeps every sample inside the hypothesis `1 ≤ n`.
#eval Plausible.Testable.check (∀ n : Nat, factorial (n + 1) < factorial (n + 2))

example :
    (List.range 20).all (fun n =>
      if 1 ≤ n then decide (factorial n < factorial (n + 1)) else true) = true := by
  native_decide

-- PBT: factorial_self_le_prop
#eval Plausible.Testable.check (∀ n : Nat, n ≤ factorial n)

example : (List.range 25).all (fun n => decide (n ≤ factorial n)) = true := by
  native_decide

-- PBT: factorial_eq_mathlib_prop
#eval Plausible.Testable.check (∀ n : Nat, factorial n = Nat.factorial n)

example : (List.range 20).all (fun n => factorial n == Nat.factorial n) = true := by
  native_decide

-- PBT: factorial_eq_one_prop
#eval Plausible.Testable.check (∀ n : Nat, factorial n = 1 ↔ n ≤ 1)

example :
    (List.range 20).all (fun n =>
      ((factorial n == 1) == decide (n ≤ 1))) = true := by
  native_decide

-- PBT: factorial_prod_prop
#eval Plausible.Testable.check
  (∀ n : Nat, factorial n = Finset.prod (Finset.Icc 1 n) id)

example :
    (List.range 15).all (fun n =>
      factorial n == Finset.prod (Finset.Icc 1 n) id) = true := by
  native_decide

-- PBT: prog_nat_prop
#eval Plausible.Testable.check (∀ n : Nat, prog (.int (n : Int)) = .ok (factorial n))

example :
    (List.range 20).all (fun n =>
      decide (prog (.int (n : Int)) = .ok (factorial n))) = true := by
  native_decide

-- PBT: prog_neg_prop
-- Every sample is a negative integer, so the hypothesis `n < 0` holds.
#eval Plausible.Testable.check
  (∀ k : Nat,
    prog (.int (-(Int.ofNat (k + 1)))) = .error (errMsg (toString (-(Int.ofNat (k + 1))))))

example :
    ((List.range 20).map fun i => (-(i + 1) : Int)).all (fun n =>
      decide (prog (.int n) = .error (errMsg (toString n)))) = true := by
  native_decide

-- PBT: prog_float_prop
-- Plausible has no `Float` sampler, so this property is checked on a
-- fixed battery of floats (negatives, zero, the Python input `3.14`,
-- and a large value). The universal statement is `prog_float_thm`.
example :
    ([(-1.5 : Float), 0.0, 3.14, 1.0, 10.0, 1e20].all fun y =>
      decide (prog (.float y) = .error (errMsg (toString y)))) = true := by
  native_decide

-- PBT: pre_iff_nat_prop
#eval Plausible.Testable.check (∀ n : Nat, Pre (.int (n : Int)))

-- Every sample is negative, so the `n < 0` side of `pre_iff_nat_prop` is exercised.
#eval Plausible.Testable.check
  (∀ k : Nat, ¬ Pre (.int (-(Int.ofNat (k + 1)))))

example :
    ([(-2.0 : Float), 0.0, 3.14].all fun y => decide (¬ Pre (.float y))) = true := by
  native_decide

example :
    (List.range 20).all (fun n => decide (Pre (.int (n : Int)))) = true := by
  native_decide

-- PBT: result_prop, on admissible inputs (the antecedent `Pre` holds)
#eval Plausible.Testable.check
  (∀ n : Nat,
    prog (.int (n : Int)) = .ok (factorial n) ∧ 0 < factorial n)

-- PBT: Post_prop on admissible inputs, including the factorial laws used
-- inside the post-condition.
#eval Plausible.Testable.check
  (∀ n : Nat,
    prog (.int (n : Int)) = .ok (factorial n) ∧
    prog (.int (n : Int)) = .ok (Nat.factorial n) ∧
    factorial (n + 1) = factorial n * (n + 1) ∧
    0 < factorial n ∧
    n ≤ factorial n ∧
    factorial n = Finset.prod (Finset.Icc 1 n) id)

-- `Post_prop` contains universal laws (including a quantifier over `Float`),
-- so it is not decided as a whole. This checks its executable content on
-- each small natural number: the result, positivity, the recurrence, and
-- the product formula.
example :
    (List.range 12).all (fun n =>
      decide (
        prog (.int (n : Int)) = .ok (factorial n) ∧
        prog (.int (n : Int)) = .ok (Nat.factorial n) ∧
        0 < factorial n ∧
        n ≤ factorial n ∧
        factorial (n + 1) = factorial n * (n + 1) ∧
        factorial n = Finset.prod (Finset.Icc 1 n) id)) = true := by
  native_decide

/-! ## Correctness: Pre → Post -/

theorem correctness_thm (x : Input) (hx : Pre x) : Post_prop x (prog x) := by
  refine ⟨
    factorial_zero_thm,
    factorial_one_thm,
    factorial_succ_thm,
    factorial_pos_thm,
    factorial_mono_thm,
    factorial_strict_succ_thm,
    factorial_self_le_thm,
    factorial_eq_mathlib_thm,
    factorial_eq_one_thm,
    factorial_prod_thm,
    prog_nat_thm,
    prog_neg_thm,
    prog_float_thm,
    pre_iff_nat_thm,
    ?_⟩
  intro _
  rcases (pre_iff_nat_thm x).mp hx with ⟨n, hn⟩
  refine ⟨n, hn, ?_, ?_⟩
  · rw [hn]
    exact prog_nat_thm n
  · exact factorial_pos_thm n

/-! ## Imperative implementation

Mirrors the Python control flow with mutable state:

* non-integers and negative integers raise `ValueError`;
* `n = 0` returns `1` immediately;
* otherwise `result` starts at `1` and is multiplied by each `i` in `1 .. n`.
-/

/-- Imperative factorial, including the Python `n == 0` early return. -/
def factorialImp (n : Nat) : Nat :=
  Id.run do
    if n == 0 then
      return 1
    let mut result : Nat := 1
    for i in List.range' 1 n do
      result := result * i
    return result

/-- Imperative program: precondition check, then the mutable product. -/
def progImp (x : Input) : Except String Nat :=
  Id.run do
    match x with
    | .float y =>
      return .error (errMsg (toString y))
    | .int n =>
      if n < 0 then
        return .error (errMsg (toString n))
      return .ok (factorialImp n.toNat)

/-! ## Imperative tests -/

example : factorialImp 0 = 1 := by native_decide

example : factorialImp 1 = 1 := by native_decide

example : factorialImp 3 = 6 := by native_decide

example : factorialImp 5 = 120 := by native_decide

example : factorialImp 10 = 3628800 := by native_decide

example : progImp (.int 3) = .ok 6 := by native_decide

example : progImp (.int 0) = .ok 1 := by native_decide

example : progImp (.int (-1)) = .error (errMsg (toString (-1 : Int))) := by native_decide

example : progImp (.float (3.14 : Float)) = .error (errMsg (toString (3.14 : Float))) := by
  native_decide

#eval factorialImp 0

#eval factorialImp 3

#eval factorialImp 8

#eval progImp (.int 3)

#eval progImp (.int 0)

#eval progImp (.int (-1))

#eval progImp (.float (3.14 : Float))

example : (List.range 20).all (fun n => factorial n == factorialImp n) = true := by
  native_decide

/-! ## Equivalence: functional = imperative -/

/-- Identity-monad reductions used to relate `do` notation to `foldl`. -/
private theorem id_pure_eq (a : α) : (pure a : Id α) = a := rfl

private theorem id_bind_eq (x : Id α) (f : α → Id β) : x >>= f = f x := rfl

/-- A `for` loop that only yields `acc * i` is the corresponding fold. -/
private theorem id_forIn_mul (l : List Nat) (init : Nat) :
    forIn (m := Id) l init (fun i r => pure (ForInStep.yield (r * i)))
      = l.foldl (fun acc i => acc * i) init := by
  induction l generalizing init with
  | nil =>
    rw [List.forIn_nil, id_pure_eq, List.foldl_nil]
  | cons a as ih =>
    rw [List.forIn_cons, id_bind_eq]
    dsimp
    exact ih (init * a)

theorem factorial_equiv_thm (n : Nat) : factorial n = factorialImp n := by
  cases n with
  | zero =>
    simp [factorial, factorialImp, Id.run, id_pure_eq]
  | succ n =>
    unfold factorial factorialImp
    simp only [Id.run]
    have hif : ((n + 1) == 0) = false := by simp
    simp only [hif, id_bind_eq, id_pure_eq]
    exact (id_forIn_mul (List.range' 1 (n + 1)) 1).symm

theorem prog_equiv_thm (x : Input) : prog x = progImp x := by
  cases x with
  | float y =>
    simp [prog, progImp, Id.run, id_pure_eq]
  | int n =>
    by_cases h : 0 ≤ n
    · have hnot : ¬ n < 0 := (Int.not_lt).mpr h
      simp [prog, progImp, h, hnot, Id.run, factorial_equiv_thm, id_pure_eq, id_bind_eq]
    · have hlt : n < 0 := lt_of_not_ge h
      simp [prog, progImp, h, hlt, Id.run, id_pure_eq]

end «16_MyFactorial»
