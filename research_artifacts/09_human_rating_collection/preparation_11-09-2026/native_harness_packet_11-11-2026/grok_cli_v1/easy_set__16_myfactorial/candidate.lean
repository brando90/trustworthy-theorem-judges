import Mathlib
import Plausible

/-!
# 16_MyFactorial

Lean 4 formalization of a Python factorial program.

Python returns `n!` for a non-negative integer `n`, with the edge cases
`factorial(0) = 1` and `factorial(1) = 1`. The value is computed by
`result = 1; for i in range(1, n + 1): result *= i`.
If the input is not a non-negative integer — a negative integer, or a
non-integer such as the float `3.14` — Python raises
`ValueError("Input must be a non-negative integer (got n=...)")`.

The mathematical content lives on `Nat` (unbounded, matching Python `int`).
Dynamic inputs are an `Input`: `ofInt` for a Python `int`, and `nonInteger`
for every other value. `nonInteger` carries the text Python would interpolate
into the error (so `3.14` is `nonInteger "3.14"`). No floating-point
arithmetic is involved; the only specified behaviour for those inputs is
`ValueError`.
-/

namespace «16_MyFactorial»

/-- Message of the Python `ValueError`. -/
def errMsg (shown : String) : String :=
  "Input must be a non-negative integer (got n=" ++ shown ++ ")"

/-- Python-style argument of `prog`.

`ofInt n` is a Python `int` (negative integers included).
`nonInteger shown` is any non-`int`; `shown` is the text placed in the error,
exactly as Python's f-string renders the rejected value. -/
inductive Input where
  | ofInt : Int → Input
  | nonInteger : String → Input
  deriving DecidableEq, Repr

/-- Text Python interpolates into the `ValueError`. -/
def inputRepr : Input → String
  | .ofInt n => toString n
  | .nonInteger shown => shown

/-- Python `pre`: the input is a non-negative integer. -/
def pre (x : Input) : Bool :=
  match x with
  | .ofInt n => decide (0 ≤ n)
  | .nonInteger _ => false

/-- Outcome of `prog`: a factorial, or the Python `ValueError`. -/
inductive Result (α : Type) where
  | ok : α → Result α
  | valueError : String → Result α
  deriving DecidableEq, Repr

/-- Functional body of the Python loop on a value already known to be a natural number.

`range(1, n + 1)` is empty when `n = 0`, so the product is `1`, in agreement
with the explicit `if n == 0: return 1` branch. -/
def factorial (n : Nat) : Nat :=
  (List.range' 1 n).foldl (fun result i => result * i) 1

/-- Functional translation of Python `prog`. -/
def prog (x : Input) : Result Nat :=
  if pre x then
    match x with
    | .ofInt n => .ok (factorial n.toNat)
    | .nonInteger shown => .valueError (errMsg shown)
  else
    .valueError (errMsg (inputRepr x))

/-! ## Unit tests -/

example : prog (.ofInt 3) = .ok 6 := by native_decide

example : prog (.ofInt 0) = .ok 1 := by native_decide

example : prog (.ofInt 1) = .ok 1 := by native_decide

example : prog (.ofInt 4) = .ok 24 := by native_decide

example : prog (.ofInt 5) = .ok 120 := by native_decide

example : prog (.ofInt 6) = .ok 720 := by native_decide

example : prog (.ofInt (-1)) = .valueError (errMsg "-1") := by native_decide

example : prog (.nonInteger "3.14") = .valueError (errMsg "3.14") := by native_decide

example : pre (.ofInt 0) = true := by native_decide

example : pre (.ofInt 7) = true := by native_decide

example : pre (.ofInt (-1)) = false := by native_decide

example : pre (.nonInteger "3.14") = false := by native_decide

#eval prog (.ofInt 3)
#eval prog (.ofInt 0)
#eval prog (.ofInt 1)
#eval prog (.ofInt 10)
#eval prog (.ofInt (-1))
#eval prog (.nonInteger "3.14")
#eval factorial 7

/-! ## Pre-condition -/

/-- The input is a non-negative integer: some `n : Nat` viewed as a Python `int`. -/
def Pre (x : Input) : Prop :=
  ∃ n : Nat, x = .ofInt (n : Int)

/-! ## Properties -/

/-- `factorial(0) = 1`, as stated in the Python docstring. -/
def factorial_zero_prop : Prop :=
  factorial 0 = 1

/-- `factorial(1) = 1`, as stated in the Python docstring. -/
def factorial_one_prop : Prop :=
  factorial 1 = 1

/-- One step of the loop: multiplying by the next integer. -/
def factorial_succ_prop (n : Nat) : Prop :=
  factorial (n + 1) = (n + 1) * factorial n

/-- The Python loop returns the product of `range(1, n + 1)`. -/
def factorial_prod_prop (n : Nat) : Prop :=
  factorial n = ∏ i ∈ Finset.Ico 1 (n + 1), i

/-- A factorial of a natural number is strictly positive. -/
def factorial_pos_prop (n : Nat) : Prop :=
  0 < factorial n

/-- `n ≤ n!`. -/
def factorial_self_le_prop (n : Nat) : Prop :=
  n ≤ factorial n

/-- Factorial is monotone. -/
def factorial_mono_prop (m n : Nat) : Prop :=
  m ≤ n → factorial m ≤ factorial n

/-- The two docstring edge cases are exactly the inputs whose factorial is `1`. -/
def factorial_eq_one_prop (n : Nat) : Prop :=
  factorial n = 1 ↔ n ≤ 1

/-- Every integer in `1 .. n` divides `n!` (each factor of the Python loop). -/
def factorial_dvd_prop (k n : Nat) : Prop :=
  0 < k → k ≤ n → k ∣ factorial n

/-- The loop agrees with Mathlib's mathematical factorial. -/
def factorial_mathlib_prop (n : Nat) : Prop :=
  factorial n = Nat.factorial n

/-- On a non-negative integer, `prog` returns the loop's factorial. -/
def prog_ok_prop (n : Nat) : Prop :=
  prog (.ofInt (n : Int)) = .ok (factorial n)

/-- On a non-negative integer, `prog` returns the product of `range(1, n + 1)`. -/
def prog_prod_prop (n : Nat) : Prop :=
  prog (.ofInt (n : Int)) = .ok (∏ i ∈ Finset.Ico 1 (n + 1), i)

/-- A negative integer violates `pre` and raises `ValueError`. -/
def prog_neg_prop (n : Int) : Prop :=
  n < 0 → prog (.ofInt n) = .valueError (errMsg (toString n))

/-- A non-integer (the Python test uses the float `3.14`) raises `ValueError`. -/
def prog_nonint_prop (shown : String) : Prop :=
  prog (.nonInteger shown) = .valueError (errMsg shown)

/-- Executable `pre` accepts an input exactly when `Pre` holds. -/
def pre_spec_prop (x : Input) : Prop :=
  pre x = true ↔ Pre x

/-- Complete case split of Python `prog`, including both `ValueError` branches. -/
def prog_cases_prop (x : Input) : Prop :=
  match x with
  | .nonInteger shown => prog x = .valueError (errMsg shown)
  | .ofInt n =>
    if 0 ≤ n then prog x = .ok (factorial n.toNat)
    else prog x = .valueError (errMsg (toString n))

/-- Under `Pre`, the input is a natural number and `prog` returns its factorial. -/
def success_prop (x : Input) : Prop :=
  ∃ n : Nat, x = .ofInt (n : Int) ∧ prog x = .ok (factorial n)

theorem factorial_mathlib_thm (n : Nat) : factorial_mathlib_prop n := by
  simp only [factorial_mathlib_prop]
  induction n with
  | zero =>
    simp [factorial]
  | succ n ih =>
    have hrange : List.range' 1 (n + 1) = List.range' 1 n ++ [n + 1] := by
      simpa [Nat.add_comm 1 n] using (List.range'_append_1 (s := 1) (m := n) (n := 1)).symm
    unfold factorial at ih ⊢
    rw [hrange, List.foldl_append, List.foldl_cons, List.foldl_nil, ih, Nat.factorial_succ,
      Nat.mul_comm]

theorem factorial_zero_thm : factorial_zero_prop := by
  simp [factorial_zero_prop, factorial]

theorem factorial_one_thm : factorial_one_prop := by
  simpa [factorial_one_prop, factorial_mathlib_prop] using factorial_mathlib_thm 1

theorem factorial_succ_thm (n : Nat) : factorial_succ_prop n := by
  simp only [factorial_succ_prop]
  have hn := factorial_mathlib_thm n
  have hs := factorial_mathlib_thm (n + 1)
  simp only [factorial_mathlib_prop] at hn hs
  rw [hn, hs, Nat.factorial_succ]

theorem factorial_prod_thm (n : Nat) : factorial_prod_prop n := by
  simp only [factorial_prod_prop]
  have hn := factorial_mathlib_thm n
  simp only [factorial_mathlib_prop] at hn
  rw [hn]
  simpa using (Finset.prod_Ico_id_eq_factorial n).symm

theorem factorial_pos_thm (n : Nat) : factorial_pos_prop n := by
  simp only [factorial_pos_prop]
  have hn := factorial_mathlib_thm n
  simp only [factorial_mathlib_prop] at hn
  rw [hn]
  exact Nat.factorial_pos n

theorem factorial_self_le_thm (n : Nat) : factorial_self_le_prop n := by
  simp only [factorial_self_le_prop]
  have hn := factorial_mathlib_thm n
  simp only [factorial_mathlib_prop] at hn
  rw [hn]
  exact Nat.self_le_factorial n

theorem factorial_mono_thm (m n : Nat) : factorial_mono_prop m n := by
  intro hmn
  simp only [factorial_mono_prop] at *
  have hm := factorial_mathlib_thm m
  have hn := factorial_mathlib_thm n
  simp only [factorial_mathlib_prop] at hm hn
  rw [hm, hn]
  exact Nat.factorial_le hmn

theorem factorial_eq_one_thm (n : Nat) : factorial_eq_one_prop n := by
  simp only [factorial_eq_one_prop]
  have hn := factorial_mathlib_thm n
  simp only [factorial_mathlib_prop] at hn
  rw [hn]
  exact Nat.factorial_eq_one

theorem factorial_dvd_thm (k n : Nat) : factorial_dvd_prop k n := by
  intro hk hkn
  simp only [factorial_dvd_prop] at *
  have hn := factorial_mathlib_thm n
  simp only [factorial_mathlib_prop] at hn
  rw [hn]
  exact Nat.dvd_factorial hk hkn

theorem prog_ok_thm (n : Nat) : prog_ok_prop n := by
  simp only [prog_ok_prop]
  have hp : pre (.ofInt (n : Int)) = true := by
    simp [pre, decide_eq_true_eq, Int.natCast_nonneg]
  simp [prog, hp, Int.toNat_natCast]

theorem prog_prod_thm (n : Nat) : prog_prod_prop n := by
  simp only [prog_prod_prop]
  have hok := prog_ok_thm n
  simp only [prog_ok_prop] at hok
  rw [hok]
  exact congrArg Result.ok (factorial_prod_thm n)

theorem prog_neg_thm (n : Int) : prog_neg_prop n := by
  intro hn
  have hp : pre (.ofInt n) = false := by
    simp only [pre]
    exact decide_eq_false (not_le_of_gt hn)
  simp [prog, hp, inputRepr]

theorem prog_nonint_thm (shown : String) : prog_nonint_prop shown := by
  simp [prog_nonint_prop, prog, pre, inputRepr]

theorem pre_spec_thm (x : Input) : pre_spec_prop x := by
  simp only [pre_spec_prop, Pre]
  cases x with
  | nonInteger shown =>
    simp [pre]
  | ofInt n =>
    constructor
    · intro h
      have hle : 0 ≤ n := of_decide_eq_true (by simpa [pre] using h)
      refine ⟨n.toNat, ?_⟩
      apply congrArg Input.ofInt
      exact (Int.toNat_of_nonneg hle).symm
    · rintro ⟨k, hk⟩
      subst hk
      simp [pre, decide_eq_true_eq, Int.natCast_nonneg]

theorem prog_cases_thm (x : Input) : prog_cases_prop x := by
  cases x with
  | nonInteger shown =>
    simp [prog_cases_prop, prog_nonint_thm, prog_nonint_prop]
  | ofInt n =>
    simp only [prog_cases_prop]
    by_cases hle : 0 ≤ n
    · have hp : pre (.ofInt n) = true := by
        simp [pre, decide_eq_true_eq, hle]
      simp [prog, hp, hle, Int.toNat_of_nonneg hle]
    · have hn : n < 0 := lt_of_not_ge hle
      have herr := prog_neg_thm n hn
      simp [hle, herr]

theorem success_thm (x : Input) (hx : Pre x) : success_prop x := by
  obtain ⟨n, rfl⟩ := hx
  refine ⟨n, rfl, ?_⟩
  have hok := prog_ok_thm n
  simp only [prog_ok_prop] at hok
  exact hok

/-! ## Post-condition -/

/-- Post-condition under `Pre`.

The input is a natural number `n` and `prog` returns `n!` as computed by the
Python loop. That value satisfies the docstring edge cases, the recurrence,
the range product, positivity, monotonicity, the characterization of `n! = 1`,
divisibility by every loop factor, and Mathlib's factorial. -/
def Post_prop (x : Input) : Prop :=
  success_prop x
    ∧ factorial_zero_prop
    ∧ factorial_one_prop
    ∧ (∀ n, factorial_succ_prop n)
    ∧ (∀ n, factorial_pos_prop n)
    ∧ (∀ n, factorial_prod_prop n)
    ∧ (∀ n, factorial_self_le_prop n)
    ∧ (∀ m n, factorial_mono_prop m n)
    ∧ (∀ n, factorial_eq_one_prop n)
    ∧ (∀ k n, factorial_dvd_prop k n)
    ∧ (∀ n, factorial_mathlib_prop n)

/-! ## Property-based tests

Executable checks of each `_prop` and of `Post_prop`.
Randomized checks use Plausible; bounded checks exhaust `List.range`.
-/

private def pbtCfg : Plausible.Configuration :=
  { numInst := 25, maxSize := 16, quiet := true }

-- factorial_zero_prop (single input)
example : factorial 0 = 1 := by native_decide

-- factorial_one_prop (single input)
example : factorial 1 = 1 := by native_decide

-- factorial_succ_prop
example : (List.range 30).all (fun n => factorial (n + 1) == (n + 1) * factorial n) = true := by
  native_decide

#eval Plausible.Testable.check (∀ n : Nat, factorial (n + 1) = (n + 1) * factorial n) pbtCfg

-- factorial_prod_prop
example :
    (List.range 20).all (fun n => factorial n == (Finset.Ico 1 (n + 1)).prod id) = true := by
  native_decide

#eval Plausible.Testable.check
    (∀ n : Nat, factorial n = ∏ i ∈ Finset.Ico 1 (n + 1), i) pbtCfg

-- factorial_pos_prop
example : (List.range 30).all (fun n => decide (0 < factorial n)) = true := by native_decide

#eval Plausible.Testable.check (∀ n : Nat, 0 < factorial n) pbtCfg

-- factorial_self_le_prop
example : (List.range 30).all (fun n => decide (n ≤ factorial n)) = true := by native_decide

#eval Plausible.Testable.check (∀ n : Nat, n ≤ factorial n) pbtCfg

-- factorial_mono_prop
example :
    (List.range 12).all (fun m =>
      (List.range 12).all (fun n =>
        decide (m ≤ n → factorial m ≤ factorial n))) = true := by
  native_decide

#eval Plausible.Testable.check (∀ m n : Nat, m ≤ n → factorial m ≤ factorial n) pbtCfg

-- factorial_eq_one_prop
example :
    (List.range 20).all (fun n => decide (factorial n = 1 ↔ n ≤ 1)) = true := by
  native_decide

#eval Plausible.Testable.check (∀ n : Nat, factorial n = 1 ↔ n ≤ 1) pbtCfg

-- factorial_dvd_prop
example :
    (List.range 12).all (fun k =>
      (List.range 12).all (fun n =>
        decide (0 < k → k ≤ n → k ∣ factorial n))) = true := by
  native_decide

#eval Plausible.Testable.check (∀ k n : Nat, 0 < k → k ≤ n → k ∣ factorial n) pbtCfg

-- factorial_mathlib_prop
example : (List.range 25).all (fun n => factorial n == Nat.factorial n) = true := by
  native_decide

#eval Plausible.Testable.check (∀ n : Nat, factorial n = Nat.factorial n) pbtCfg

-- prog_ok_prop
example :
    (List.range 25).all (fun n => prog (.ofInt (n : Int)) == .ok (factorial n)) = true := by
  native_decide

#eval Plausible.Testable.check
    (∀ n : Nat, prog (.ofInt (n : Int)) = .ok (factorial n)) pbtCfg

-- prog_prod_prop
example :
    (List.range 20).all (fun n =>
      prog (.ofInt (n : Int)) == .ok ((Finset.Ico 1 (n + 1)).prod id)) = true := by
  native_decide

#eval Plausible.Testable.check
    (∀ n : Nat, prog (.ofInt (n : Int)) = .ok (∏ i ∈ Finset.Ico 1 (n + 1), i)) pbtCfg

-- prog_neg_prop
example :
    (List.range 30).all (fun i =>
      let n : Int := -(i + 1)
      prog (.ofInt n) == .valueError (errMsg (toString n))) = true := by
  native_decide

#eval Plausible.Testable.check
    (∀ n : Int, n < 0 → prog (.ofInt n) = .valueError (errMsg (toString n))) pbtCfg

-- prog_nonint_prop, including the Python test value 3.14
example : prog (.nonInteger "3.14") = .valueError (errMsg "3.14") := by native_decide

example :
    ["3.14", "0.0", "-2.5", "True", "hello", ""].all (fun s =>
      prog (.nonInteger s) == .valueError (errMsg s)) = true := by
  native_decide

#eval Plausible.Testable.check
    (∀ shown : String, prog (.nonInteger shown) = .valueError (errMsg shown)) pbtCfg

-- pre_spec_prop, executable on each constructor
example : (List.range 30).all (fun n => pre (.ofInt (n : Int)) = true) = true := by
  native_decide

example :
    (List.range 30).all (fun i => pre (.ofInt (-(i + 1) : Int)) = false) = true := by
  native_decide

example :
    ["3.14", "-1.0", "x"].all (fun s => pre (.nonInteger s) = false) = true := by
  native_decide

#eval Plausible.Testable.check (∀ n : Nat, pre (.ofInt (n : Int)) = true) pbtCfg

#eval Plausible.Testable.check (∀ n : Int, n < 0 → pre (.ofInt n) = false) pbtCfg

#eval Plausible.Testable.check (∀ shown : String, pre (.nonInteger shown) = false) pbtCfg

-- prog_cases_prop, executable on naturals, negatives, and non-integers
example :
    (List.range 20).all (fun n =>
      prog (.ofInt (n : Int)) == .ok (factorial n)) = true := by
  native_decide

example :
    (List.range 20).all (fun i =>
      let n : Int := -(i + 1)
      prog (.ofInt n) == .valueError (errMsg (toString n))) = true := by
  native_decide

-- success_prop on every canonical pre-satisfying input
example :
    (List.range 20).all (fun n =>
      decide (success_prop (.ofInt (n : Int)))) = true := by
  native_decide

-- Post_prop on every canonical pre-satisfying input.
-- `Post_prop (.ofInt n)` packages `success_prop` together with the factorial laws above;
-- those laws are checked individually, and this check ties them to `prog`'s result.
example :
    (List.range 15).all (fun n =>
      let x := Input.ofInt (n : Int)
      pre x = true
        && prog x == .ok (factorial n)
        && factorial 0 == 1
        && factorial 1 == 1
        && factorial (n + 1) == (n + 1) * factorial n
        && decide (0 < factorial n)
        && factorial n == (Finset.Ico 1 (n + 1)).prod id
        && decide (n ≤ factorial n)
        && decide (n ≤ n → factorial n ≤ factorial n)
        && decide (factorial n = 1 ↔ n ≤ 1)
        && decide (0 < n + 1 → n + 1 ≤ n + 1 → (n + 1) ∣ factorial (n + 1))
        && factorial n == Nat.factorial n) = true := by
  native_decide

#eval Plausible.Testable.check
    (∀ n : Nat,
      prog (.ofInt (n : Int)) = .ok (factorial n)
        ∧ factorial 0 = 1
        ∧ factorial (n + 1) = (n + 1) * factorial n
        ∧ 0 < factorial n
        ∧ factorial n = Nat.factorial n) pbtCfg

/-! ## Correctness -/

theorem correctness_thm (x : Input) (hx : Pre x) : Post_prop x := by
  refine ⟨success_thm x hx,
    factorial_zero_thm,
    factorial_one_thm,
    factorial_succ_thm,
    factorial_pos_thm,
    factorial_prod_thm,
    factorial_self_le_thm,
    factorial_mono_thm,
    factorial_eq_one_thm,
    factorial_dvd_thm,
    factorial_mathlib_thm⟩

/-! ## Imperative implementation -/

/-- Imperative loop, mirroring Python's `result` accumulator and the `n == 0` return. -/
def factorialImp (n : Nat) : Nat :=
  Id.run do
    if n == 0 then
      return 1
    let mut result : Nat := 1
    for i in List.range' 1 n do
      result := result * i
    return result

/-- Imperative translation of Python `prog`: the same `pre` guard, then the loop. -/
def progImp (x : Input) : Result Nat :=
  if pre x then
    match x with
    | .ofInt n => .ok (factorialImp n.toNat)
    | .nonInteger shown => .valueError (errMsg shown)
  else
    .valueError (errMsg (inputRepr x))

/-! ## Imperative tests -/

example : factorialImp 0 = 1 := by native_decide

example : factorialImp 1 = 1 := by native_decide

example : factorialImp 3 = 6 := by native_decide

example : factorialImp 5 = 120 := by native_decide

example : factorialImp 7 = 5040 := by native_decide

example : progImp (.ofInt 3) = .ok 6 := by native_decide

example : progImp (.ofInt 0) = .ok 1 := by native_decide

example : progImp (.ofInt 1) = .ok 1 := by native_decide

example : progImp (.ofInt 6) = .ok 720 := by native_decide

example : progImp (.ofInt (-1)) = .valueError (errMsg "-1") := by native_decide

example : progImp (.nonInteger "3.14") = .valueError (errMsg "3.14") := by native_decide

example :
    (List.range 25).all (fun n => factorialImp n == factorial n) = true := by
  native_decide

example :
    (List.range 20).all (fun n =>
      prog (.ofInt (n : Int)) == progImp (.ofInt (n : Int))) = true := by
  native_decide

example :
    (List.range 20).all (fun i =>
      let n : Int := -(i + 1)
      prog (.ofInt n) == progImp (.ofInt n)) = true := by
  native_decide

example :
    ["3.14", "0.5", ""].all (fun s =>
      prog (.nonInteger s) == progImp (.nonInteger s)) = true := by
  native_decide

#eval factorialImp 0
#eval factorialImp 3
#eval factorialImp 8
#eval progImp (.ofInt 4)
#eval progImp (.ofInt (-2))
#eval progImp (.nonInteger "3.14")

/-! ## Equivalence -/

theorem factorialImp_eq_factorial (n : Nat) : factorialImp n = factorial n := by
  cases n with
  | zero =>
    unfold factorialImp
    rfl
  | succ n =>
    unfold factorialImp factorial
    simp [Id.run, bind, pure]
    have hloop :=
      List.forIn_pure_yield_eq_foldl (m := Id) (l := List.range' 1 (n + 1))
        (f := fun (i r : Nat) => r * i) (init := 1)
    simpa [Id.run, bind, pure] using hloop

/-- The functional program and the imperative program agree on every input,
including both `ValueError` branches. -/
theorem equiv_thm (x : Input) : prog x = progImp x := by
  cases x with
  | nonInteger shown =>
    simp [prog, progImp]
  | ofInt n =>
    by_cases hp : pre (.ofInt n)
    · simp [prog, progImp, hp, factorialImp_eq_factorial]
    · simp [prog, progImp, hp]

end «16_MyFactorial»
