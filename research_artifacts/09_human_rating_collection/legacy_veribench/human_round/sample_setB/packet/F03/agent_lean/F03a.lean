import Mathlib

/-!
# 16_MyFactorial

Lean 4 translation of the Python program `MyFactorial`.

The Python program computes the factorial `n!` of a natural number (a non-negative
`int`).  It raises `ValueError` when the input is not a natural number
(`pre(n) = isinstance(n, int) and n >= 0`), returns `1` for `n = 0`, and otherwise
multiplies `1 * 1 * 2 * ... * n` in a `for` loop over `range(1, n + 1)`.

Contents:
* `factorial` -- functional implementation of `n!` on `Nat`.
* `prog` -- mirror of the Python `prog` on `Int`: returns `.error msg` (the raised
  `ValueError`) for negative input and `.ok (factorial n)` otherwise.
* `Pre` -- the Python precondition `n >= 0`.
* property propositions (`*_prop`) with proven theorems (`*_thm`).
* `Post_prop` -- post-condition, and the correctness theorem `Pre -> Post`.
* property-based tests (Plausible and bounded exhaustive checks).
* `factorialImp` / `progImp` -- imperative implementations with `Id.run do` and a
  mutable accumulator, together with proofs that they agree with the functional
  implementation.
-/

namespace MyFactorial

/-! ## Functional implementation -/

/-- Functional implementation of `n!` for a natural number `n`. -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-- Mirror of the Python `pre`: the input is a non-negative integer. -/
def preCheck (n : Int) : Bool := 0 ≤ n

/-- The error message raised by the Python program on a precondition violation. -/
def errorMsg (n : Int) : String := s!"Input must be a non-negative integer (got n={n})"

/-- Mirror of the Python `prog` on integers.  A negative input violates the
precondition and the Python code raises `ValueError`; this is modelled by `.error`
carrying the same message.  Otherwise the result is `n!`. -/
def prog (n : Int) : Except String Nat :=
  if preCheck n then
    .ok (factorial n.toNat)
  else
    .error (errorMsg n)

-- Decidable equality on `Except`, so that results of `prog` can be compared in tests.
deriving instance DecidableEq for Except

/-! ## Unit tests -/

-- Basic unit test: candidate(3) == 6
example : factorial 3 = 6 := by native_decide
-- Edge unit test: candidate(0) == 1
example : factorial 0 = 1 := by native_decide
example : factorial 1 = 1 := by native_decide
example : factorial 5 = 120 := by native_decide
example : factorial 10 = 3628800 := by native_decide

example : prog 3 = .ok 6 := by native_decide
example : prog 0 = .ok 1 := by native_decide
example : prog 1 = .ok 1 := by native_decide
-- Negative input: the precondition is violated and a `ValueError` is raised.
example : prog (-1) = .error "Input must be a non-negative integer (got n=-1)" := by
  native_decide
example : (prog (-1)).toOption = none := by native_decide
example : (prog (-5)).toBool = false := by native_decide

#eval factorial 3        -- 6
#eval factorial 0        -- 1
#eval prog 3             -- Except.ok 6
#eval prog 0             -- Except.ok 1
#eval prog (-1)          -- Except.error "Input must be a non-negative integer (got n=-1)"

/-! ## Pre-condition -/

/-- Precondition of the Python program: the input is a non-negative integer. -/
def Pre (n : Int) : Prop := 0 ≤ n

instance (n : Int) : Decidable (Pre n) := by unfold Pre; infer_instance

/-- The executable `preCheck` decides `Pre`. -/
theorem preCheck_iff (n : Int) : preCheck n = true ↔ Pre n := by
  simp [preCheck, Pre]

/-! ## Properties -/

/-- `factorial(0) = 1` by definition. -/
def base_prop : Prop := factorial 0 = 1

theorem base_thm : base_prop := rfl

/-- `factorial(1) = 1`. -/
def one_prop : Prop := factorial 1 = 1

theorem one_thm : one_prop := rfl

/-- Recurrence: `factorial (n + 1) = (n + 1) * factorial n`. -/
def step_prop (n : Nat) : Prop := factorial (n + 1) = (n + 1) * factorial n

theorem step_thm (n : Nat) : step_prop n := rfl

/-- The implementation agrees with Mathlib's `Nat.factorial`. -/
def spec_prop (n : Nat) : Prop := factorial n = Nat.factorial n

theorem spec_thm (n : Nat) : spec_prop n := by
  unfold spec_prop
  induction n with
  | zero => rfl
  | succ k ih => rw [factorial, Nat.factorial_succ, ih]

/-- The result is the product of `range(1, n + 1)`, exactly as the Python loop computes. -/
def prod_prop (n : Nat) : Prop := factorial n = (List.range' 1 n).prod

theorem prod_thm (n : Nat) : prod_prop n := by
  unfold prod_prop
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.range'_1_concat, List.prod_append, List.prod_singleton, factorial, ih,
      Nat.mul_comm, Nat.add_comm]

/-- The factorial is always positive. -/
def pos_prop (n : Nat) : Prop := 0 < factorial n

theorem pos_thm (n : Nat) : pos_prop n := by
  unfold pos_prop
  induction n with
  | zero => decide
  | succ k ih => exact Nat.mul_pos (Nat.succ_pos k) ih

/-- The factorial is monotone: `factorial n ≤ factorial (n + 1)`. -/
def mono_prop (n : Nat) : Prop := factorial n ≤ factorial (n + 1)

theorem mono_thm (n : Nat) : mono_prop n := by
  unfold mono_prop
  rw [factorial]
  exact Nat.le_mul_of_pos_left _ (Nat.succ_pos n)

/-- `n ≤ factorial n`. -/
def self_le_prop (n : Nat) : Prop := n ≤ factorial n

theorem self_le_thm (n : Nat) : self_le_prop n := by
  unfold self_le_prop
  have h := spec_thm n
  unfold spec_prop at h
  rw [h]
  exact Nat.self_le_factorial n

/-- `prog` raises (returns an error) exactly when the precondition fails. -/
def error_prop (n : Int) : Prop := (∃ msg, prog n = .error msg) ↔ ¬ Pre n

theorem error_thm (n : Int) : error_prop n := by
  unfold error_prop prog
  constructor
  · rintro ⟨msg, h⟩ hn
    rw [if_pos ((preCheck_iff n).2 hn)] at h
    exact absurd h (by simp)
  · intro hn
    rw [if_neg (fun h => hn ((preCheck_iff n).1 h))]
    exact ⟨_, rfl⟩

/-- The raised error carries exactly the Python message. -/
def error_msg_prop (n : Int) : Prop :=
  ¬ Pre n → prog n = .error s!"Input must be a non-negative integer (got n={n})"

theorem error_msg_thm (n : Int) : error_msg_prop n := by
  unfold error_msg_prop prog errorMsg
  intro hn
  rw [if_neg (fun h => hn ((preCheck_iff n).1 h))]

/-- On admissible inputs, `prog` succeeds and returns `n!`. -/
def ok_prop (n : Int) : Prop := Pre n → prog n = .ok (Nat.factorial n.toNat)

theorem ok_thm (n : Int) : ok_prop n := by
  unfold ok_prop prog
  intro hn
  have h := spec_thm n.toNat
  unfold spec_prop at h
  rw [if_pos ((preCheck_iff n).2 hn), h]

/-! ## Post-condition -/

/-- Post-condition relating an input `n` and the result `r` of the Python program on
an admissible input: the call succeeds (no `ValueError`), and the returned value is
`n!`, positive, equal to the product `1 * 2 * ... * n` of `range(1, n + 1)`, and equal
to `1` when `n = 0`. -/
def Post_prop (n : Int) (r : Except String Nat) : Prop :=
  ∃ v, r = .ok v ∧
    v = Nat.factorial n.toNat ∧
    0 < v ∧
    v = (List.range' 1 n.toNat).prod ∧
    (n = 0 → v = 1)

/-! ## Property-based tests -/

-- base_prop / one_prop (closed statements)
example : factorial 0 = 1 := by native_decide
example : factorial 1 = 1 := by native_decide

-- step_prop
#eval Plausible.Testable.check (∀ n : Nat, factorial (n + 1) = (n + 1) * factorial n)
example : (List.range 30).all (fun n => factorial (n + 1) == (n + 1) * factorial n) = true := by
  native_decide

-- spec_prop
#eval Plausible.Testable.check (∀ n : Nat, factorial n = Nat.factorial n)
example : (List.range 30).all (fun n => factorial n == Nat.factorial n) = true := by native_decide

-- prod_prop
#eval Plausible.Testable.check (∀ n : Nat, factorial n = (List.range' 1 n).prod)
example : (List.range 30).all (fun n => factorial n == (List.range' 1 n).prod) = true := by
  native_decide

-- pos_prop
#eval Plausible.Testable.check (∀ n : Nat, 0 < factorial n)
example : (List.range 30).all (fun n => 0 < factorial n) = true := by native_decide

-- mono_prop
#eval Plausible.Testable.check (∀ n : Nat, factorial n ≤ factorial (n + 1))
example : (List.range 30).all (fun n => factorial n ≤ factorial (n + 1)) = true := by native_decide

-- self_le_prop
#eval Plausible.Testable.check (∀ n : Nat, n ≤ factorial n)
example : (List.range 30).all (fun n => n ≤ factorial n) = true := by native_decide

-- error_prop / error_msg_prop
#eval Plausible.Testable.check (∀ n : Int, (prog n).toOption = none ↔ n < 0)
#eval Plausible.Testable.check (∀ k : Nat,
  prog (-(k : Int) - 1) = .error s!"Input must be a non-negative integer (got n={-(k : Int) - 1})")
example : (List.range 30).all (fun k => (prog (-(k : Int) - 1)).toOption == none) = true := by
  native_decide
example : (List.range 30).all (fun k =>
    prog (-(k : Int) - 1) == .error s!"Input must be a non-negative integer (got n={-(k : Int) - 1})") = true := by
  native_decide

-- ok_prop
#eval Plausible.Testable.check (∀ k : Nat, prog (k : Int) = .ok (Nat.factorial k))
example : (List.range 30).all (fun k => prog (k : Int) == .ok (Nat.factorial k)) = true := by
  native_decide

-- Post_prop (executable form)
/-- Executable form of `Post_prop`. -/
def postCheck (n : Int) (r : Except String Nat) : Bool :=
  match r with
  | .ok v => v == Nat.factorial n.toNat && 0 < v && v == (List.range' 1 n.toNat).prod &&
      (n != 0 || v == 1)
  | .error _ => false

#eval Plausible.Testable.check (∀ k : Nat, postCheck (k : Int) (prog (k : Int)) = true)
example : (List.range 30).all (fun k => postCheck (k : Int) (prog (k : Int))) = true := by
  native_decide

/-! ## Correctness theorem -/

/-- Correctness: on every input satisfying the precondition, the Python program
succeeds and its result satisfies the post-condition. -/
theorem correctness (n : Int) (hn : Pre n) : Post_prop n (prog n) := by
  unfold Post_prop
  refine ⟨factorial n.toNat, ?_, ?_, ?_, ?_, ?_⟩
  · unfold prog
    rw [if_pos ((preCheck_iff n).2 hn)]
  · exact spec_thm n.toNat
  · exact pos_thm n.toNat
  · exact prod_thm n.toNat
  · intro h
    subst h
    rfl

/-! ## Imperative implementation -/

/-- Imperative implementation mirroring the Python `prog` body: early return for
`n = 0`, then a mutable accumulator multiplied by every `i` in `range(1, n + 1)`. -/
def factorialImp (n : Nat) : Nat := Id.run do
  if n == 0 then
    return 1
  let mut result := 1
  for i in [1:n + 1] do
    result := result * i
  return result

/-- Imperative mirror of the Python `prog`, including the `ValueError` check. -/
def progImp (n : Int) : Except String Nat := Id.run do
  if !preCheck n then
    return .error (errorMsg n)
  return .ok (factorialImp n.toNat)

/-! ## Imperative tests -/

example : factorialImp 3 = 6 := by native_decide
example : factorialImp 0 = 1 := by native_decide
example : factorialImp 1 = 1 := by native_decide
example : factorialImp 5 = 120 := by native_decide
example : progImp 3 = .ok 6 := by native_decide
example : progImp 0 = .ok 1 := by native_decide
example : progImp (-1) = .error "Input must be a non-negative integer (got n=-1)" := by
  native_decide

#eval factorialImp 3     -- 6
#eval factorialImp 0     -- 1
#eval progImp (-1)

#eval Plausible.Testable.check (∀ n : Nat, factorialImp n = factorial n)
#eval Plausible.Testable.check (∀ n : Int, progImp n = prog n)
example : (List.range 30).all (fun n => factorialImp n == factorial n) = true := by native_decide
example : (List.range 30).all (fun k => progImp (k : Int) == prog (k : Int)) = true := by
  native_decide

/-! ## Equivalence theorems -/

/-- The accumulator loop over `List.range' s k` multiplies the accumulator by the
product of the list. -/
theorem forIn_range'_mul (s k acc : Nat) :
    (forIn (m := Id) (List.range' s k) acc
      (fun i r => pure (ForInStep.yield (r * i)))) = acc * (List.range' s k).prod := by
  induction k generalizing s acc with
  | zero =>
    simp only [List.range'_zero, List.forIn_nil, List.prod_nil, Nat.mul_one]
    rfl
  | succ k ih =>
    rw [List.range'_succ, List.forIn_cons]
    simp only [List.prod_cons]
    show forIn (m := Id) (List.range' (s + 1) k) (acc * s)
      (fun i r => pure (ForInStep.yield (r * i))) = acc * (s * (List.range' (s + 1) k).prod)
    rw [ih, Nat.mul_assoc]

/-- The imperative implementation agrees with the functional one. -/
theorem factorialImp_eq (n : Nat) : factorialImp n = factorial n := by
  have hprod := prod_thm n
  unfold prod_prop at hprod
  rw [hprod]
  cases n with
  | zero => rfl
  | succ k =>
    unfold factorialImp
    simp only [Id.run, Std.Range.forIn_eq_forIn_range', Std.Range.size, Nat.add_sub_cancel,
      Nat.div_one, beq_iff_eq, Nat.add_one_ne_zero, ite_false, pure_bind, bind_pure]
    rw [forIn_range'_mul, Nat.one_mul]

/-- The imperative `progImp` agrees with the functional `prog`. -/
theorem progImp_eq (n : Int) : progImp n = prog n := by
  unfold progImp prog
  cases h : preCheck n <;> simp [factorialImp_eq]

end MyFactorial
