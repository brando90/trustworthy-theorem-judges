import Mathlib

/-!
# 16_MyFactorial

Lean 4 formalization of the Python factorial program `prog(n: int) -> int` with
precondition `pre(n: int) -> bool` checking that `n` is a non-negative integer (`n >= 0`).

Edge cases and specification:
- `factorial(0) = 1` by definition
- `factorial(1) = 1`
- Raising `ValueError` when `not pre(n)` (`n < 0`) is modeled by `prog` returning `none : Option Int`,
  while valid inputs `n ≥ 0` return `some (n!)`.
-/

namespace «16_MyFactorial»

/-! ## 4. Implementation (functional definition) -/

/-- Executable precondition: `true` iff `n` is a non-negative integer (`n ≥ 0`). -/
def pre (n : Int) : Bool :=
  decide (n ≥ 0)

/-- Recursive functional helper computing `n!` on natural numbers. -/
def factorialNat : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorialNat n

/-- Functional implementation computing `n!` on integers via folding over `[1, ..., n]`.
Returns `1` when `n ≤ 0`. -/
def myFactorial (n : Int) : Int :=
  if n ≤ 0 then
    1
  else
    (List.range' 1 n.toNat).foldl (fun (acc : Int) (i : Nat) => acc * (i : Int)) 1

/-- Functional implementation of `prog(n: int)` returning `Option Int`.
Returns `none` when `pre n` is violated (`n < 0`, modeling `ValueError`),
and `some (n!)` when `n ≥ 0`. -/
def prog (n : Int) : Option Int :=
  if ¬ pre n then
    none
  else if n == 0 then
    some 1
  else
    some ((List.range' 1 n.toNat).foldl (fun (acc : Int) (i : Nat) => acc * (i : Int)) 1)

/-! ## 5. Unit tests -/

-- Basic and edge unit tests on `prog`
example : prog 3 = some 6 := by native_decide
example : prog 0 = some 1 := by native_decide
example : prog 1 = some 1 := by native_decide
example : prog 2 = some 2 := by native_decide
example : prog 4 = some 24 := by native_decide
example : prog 5 = some 120 := by native_decide

-- Negative inputs (pre-violations return `none`, corresponding to raising `ValueError`)
example : prog (-1) = none := by native_decide
example : prog (-5) = none := by native_decide

-- Unit tests on `myFactorial` and `factorialNat`
example : myFactorial 0 = 1 := by native_decide
example : myFactorial 1 = 1 := by native_decide
example : myFactorial 3 = 6 := by native_decide
example : myFactorial 5 = 120 := by native_decide
example : factorialNat 0 = 1 := by native_decide
example : factorialNat 1 = 1 := by native_decide
example : factorialNat 3 = 6 := by native_decide
example : factorialNat 5 = 120 := by native_decide

#eval prog 3
#eval prog 0
#eval prog 1
#eval prog 5
#eval prog (-1)
#eval myFactorial 3
#eval myFactorial 0

/-! ## 6. Pre-condition predicate (`def Pre`) -/

/-- Pre-condition proposition: input `n` is a non-negative integer. -/
def Pre (n : Int) : Prop :=
  n ≥ 0

instance (n : Int) : Decidable (Pre n) :=
  inferInstanceAs (Decidable (n ≥ 0))

theorem pre_iff_Pre (n : Int) : pre n = true ↔ Pre n := by
  simp [pre, Pre]

/-! ## Helper Lemmas Connecting Implementations to `Nat.factorial` -/

theorem factorialNat_eq_factorial (n : Nat) : factorialNat n = Nat.factorial n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp [factorialNat, Nat.factorial_succ, ih]

theorem foldl_range'_eq_factorial (n : Nat) :
    (List.range' 1 n).foldl (fun (acc : Int) (i : Nat) => acc * (i : Int)) 1 =
      (Nat.factorial n : Int) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range'_1_concat, List.foldl_append]
    simp [ih, Nat.factorial_succ]
    ring

theorem foldl_nat_range'_eq_factorial (n : Nat) :
    (List.range' 1 n).foldl (fun (acc : Nat) (i : Nat) => acc * i) 1 =
      Nat.factorial n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range'_1_concat, List.foldl_append]
    simp [ih, Nat.factorial_succ]
    ring

theorem list_range'_prod_eq_factorial (n : Nat) :
    (List.range' 1 n).prod = Nat.factorial n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range'_1_concat, List.prod_append]
    simp [ih, Nat.factorial_succ]
    ring

theorem myFactorial_eq_factorial (n : Int) (h : Pre n) :
    myFactorial n = (Nat.factorial n.toNat : Int) := by
  unfold myFactorial
  unfold Pre at h
  split_ifs with hle
  · have hn0 : n = 0 := by omega
    subst hn0
    simp
  · exact foldl_range'_eq_factorial n.toNat

theorem myFactorial_eq_factorialNat (n : Int) (h : Pre n) :
    myFactorial n = (factorialNat n.toNat : Int) := by
  rw [myFactorial_eq_factorial n h, factorialNat_eq_factorial]

theorem prog_eq_none_of_not_Pre (n : Int) (h : ¬ Pre n) :
    prog n = none := by
  unfold prog
  have hpre : ¬ pre n = true := by
    rw [pre_iff_Pre]
    exact h
  simp [hpre]

theorem prog_eq_some_myFactorial (n : Int) (h : Pre n) :
    prog n = some (myFactorial n) := by
  unfold prog myFactorial
  have hpre : pre n = true := (pre_iff_Pre n).mpr h
  unfold Pre at h
  by_cases hn0 : n = 0
  · subst hn0
    simp [pre]
  · have hnle : ¬ (n ≤ 0) := by omega
    simp [hpre, hn0, hnle]

/-! ## 7. Property propositions and theorems -/

/-- Property 1: When the precondition is violated (`¬ Pre n`, i.e., `n < 0`),
`prog n` returns `none` (corresponding to raising `ValueError`). -/
def invalid_input_prop (n : Int) : Prop :=
  ¬ Pre n → prog n = none

theorem invalid_input_thm (n : Int) : invalid_input_prop n := by
  intro hnot
  exact prog_eq_none_of_not_Pre n hnot

/-- Property 2: When the precondition holds, `prog n` returns `some (myFactorial n)` and `isSome`. -/
def valid_some_prop (n : Int) : Prop :=
  prog n = some (myFactorial n) ∧ (prog n).isSome = true

theorem valid_some_thm (n : Int) (h : Pre n) : valid_some_prop n := by
  have heq := prog_eq_some_myFactorial n h
  exact ⟨heq, by simp [heq]⟩

/-- Property 3: Edge case `factorial(0) = 1` by definition. -/
def base_zero_prop (n : Int) : Prop :=
  n = 0 → prog n = some 1 ∧ myFactorial n = 1

theorem base_zero_thm (n : Int) : base_zero_prop n := by
  intro hn
  subst hn
  simp [prog, pre, myFactorial]

/-- Property 4: Edge case `factorial(1) = 1`. -/
def base_one_prop (n : Int) : Prop :=
  n = 1 → prog n = some 1 ∧ myFactorial n = 1

theorem base_one_thm (n : Int) : base_one_prop n := by
  intro hn
  subst hn
  simp [prog, pre, myFactorial]

/-- Property 5: Positivity / lower bound (`n! ≥ 1` for all `n ≥ 0`). -/
def pos_prop (n : Int) : Prop :=
  myFactorial n ≥ 1 ∧ (∃ r : Int, prog n = some r ∧ r ≥ 1)

theorem pos_thm (n : Int) (h : Pre n) : pos_prop n := by
  have hfact : myFactorial n = (Nat.factorial n.toNat : Int) := myFactorial_eq_factorial n h
  have hpos_nat : 1 ≤ Nat.factorial n.toNat := Nat.factorial_pos n.toNat
  have hpos_int : myFactorial n ≥ 1 := by
    rw [hfact]
    exact_mod_cast hpos_nat
  refine ⟨hpos_int, ⟨myFactorial n, prog_eq_some_myFactorial n h, hpos_int⟩⟩

/-- Property 6: Equivalence with Mathlib's `Nat.factorial`. -/
def mathlib_eq_prop (n : Int) : Prop :=
  myFactorial n = (Nat.factorial n.toNat : Int) ∧
  prog n = some (Nat.factorial n.toNat : Int)

theorem mathlib_eq_thm (n : Int) (h : Pre n) : mathlib_eq_prop n := by
  have h1 := myFactorial_eq_factorial n h
  have h2 := prog_eq_some_myFactorial n h
  exact ⟨h1, h2.trans (congrArg some h1)⟩

/-- Property 7: Equivalence with the product of `[1, ..., n]`. -/
def range_prod_prop (n : Int) : Prop :=
  myFactorial n = ((List.range' 1 n.toNat).prod : Int) ∧
  prog n = some ((List.range' 1 n.toNat).prod : Int)

theorem range_prod_thm (n : Int) (h : Pre n) : range_prod_prop n := by
  have h1 := myFactorial_eq_factorial n h
  have h2 := prog_eq_some_myFactorial n h
  rw [← list_range'_prod_eq_factorial n.toNat] at h1
  exact ⟨h1, h2.trans (congrArg some h1)⟩

/-- Property 8: Forward recurrence `(n + 1)! = (n + 1) * n!` for `n ≥ 0`. -/
def recurrence_succ_prop (n : Int) : Prop :=
  myFactorial (n + 1) = (n + 1) * myFactorial n ∧
  prog (n + 1) = Option.map (fun r => (n + 1) * r) (prog n)

theorem recurrence_succ_thm (n : Int) (h : Pre n) : recurrence_succ_prop n := by
  have hPre_succ : Pre (n + 1) := by unfold Pre at *; omega
  have h1 := myFactorial_eq_factorial n h
  have h2 := myFactorial_eq_factorial (n + 1) hPre_succ
  have htoNat : (n + 1).toNat = n.toNat + 1 := by
    unfold Pre at h
    omega
  have hn_cast : ((n.toNat : Int) + 1) = n + 1 := by
    unfold Pre at h
    omega
  have hrec : myFactorial (n + 1) = (n + 1) * myFactorial n := by
    rw [h2, h1, htoNat, Nat.factorial_succ]
    push_cast
    rw [hn_cast]
  refine ⟨hrec, ?_⟩
  rw [prog_eq_some_myFactorial (n + 1) hPre_succ, prog_eq_some_myFactorial n h, hrec]
  rfl

/-- Property 9: Backward recurrence `n! = n * (n - 1)!` for `n > 0`. -/
def recurrence_pred_prop (n : Int) : Prop :=
  n > 0 →
    myFactorial n = n * myFactorial (n - 1) ∧
    prog n = Option.map (fun r => n * r) (prog (n - 1))

theorem recurrence_pred_thm (n : Int) (_h : Pre n) : recurrence_pred_prop n := by
  intro hpos
  have hPre_pred : Pre (n - 1) := by unfold Pre; omega
  have hsucc := recurrence_succ_thm (n - 1) hPre_pred
  have heq : n - 1 + 1 = n := by ring
  rcases hsucc with ⟨h1, h2⟩
  rw [heq] at h1 h2
  exact ⟨h1, h2⟩

/-- Property 10: Step monotonicity `n! ≤ (n + 1)!` for `n ≥ 0`. -/
def mono_step_prop (n : Int) : Prop :=
  myFactorial n ≤ myFactorial (n + 1)

theorem mono_step_thm (n : Int) (h : Pre n) : mono_step_prop n := by
  unfold mono_step_prop
  have hrec := (recurrence_succ_thm n h).1
  have hpos := (pos_thm n h).1
  have hn1 : n + 1 ≥ 1 := by unfold Pre at h; omega
  rw [hrec]
  nlinarith

/-- Property 10b: General two-variable monotonicity `0 ≤ m ≤ n → m! ≤ n!`. -/
def mono_le_prop (m n : Int) : Prop :=
  Pre m → m ≤ n → myFactorial m ≤ myFactorial n

theorem mono_le_thm (m n : Int) : mono_le_prop m n := by
  intro hm hmn
  have hn : Pre n := by unfold Pre at *; omega
  rw [myFactorial_eq_factorial m hm, myFactorial_eq_factorial n hn]
  have hle_nat : m.toNat ≤ n.toNat := by unfold Pre at hm; omega
  exact_mod_cast Nat.factorial_le hle_nat

/-- Property 11: Strict monotonicity `n! < (n + 1)!` for `n ≥ 1`. -/
def strict_mono_prop (n : Int) : Prop :=
  n ≥ 1 → myFactorial n < myFactorial (n + 1)

theorem strict_mono_thm (n : Int) (h : Pre n) : strict_mono_prop n := by
  intro hn1
  have hrec := (recurrence_succ_thm n h).1
  have hpos := (pos_thm n h).1
  rw [hrec]
  nlinarith

/-- Property 12: Self-divisibility `n ∣ n!` for `n ≥ 1`. -/
def dvd_prop (n : Int) : Prop :=
  n ≥ 1 → n ∣ myFactorial n

theorem dvd_thm (n : Int) (h : Pre n) : dvd_prop n := by
  intro hn1
  have hpos : n > 0 := by omega
  have hrec := (recurrence_pred_thm n h hpos).1
  exact ⟨myFactorial (n - 1), hrec⟩

/-- Property 12b: Divisibility by any factor `1 ≤ k ≤ n` (`k ∣ n!`). -/
def dvd_of_le_prop (k n : Int) : Prop :=
  1 ≤ k → k ≤ n → k ∣ myFactorial n

theorem dvd_of_le_thm (k n : Int) : dvd_of_le_prop k n := by
  intro hk1 hkn
  have hn : Pre n := by unfold Pre; omega
  rw [myFactorial_eq_factorial n hn]
  have hk_pos : 0 < k.toNat := by omega
  have hkn_nat : k.toNat ≤ n.toNat := by omega
  have hdvd_nat : k.toNat ∣ Nat.factorial n.toNat := Nat.dvd_factorial hk_pos hkn_nat
  have hk_cast : (k.toNat : Int) = k := by omega
  rw [← hk_cast]
  exact_mod_cast hdvd_nat

/-- Property 13: Evenness `2 ∣ n!` for `n ≥ 2`. -/
def even_prop (n : Int) : Prop :=
  n ≥ 2 → 2 ∣ myFactorial n

theorem even_thm (n : Int) (_h : Pre n) : even_prop n := by
  intro hn2
  exact dvd_of_le_thm 2 n (by decide) hn2

/-- Property 14: Lower bound `n! ≥ n` for `n ≥ 0`. -/
def ge_self_prop (n : Int) : Prop :=
  myFactorial n ≥ n

theorem ge_self_thm (n : Int) (h : Pre n) : ge_self_prop n := by
  unfold ge_self_prop
  rw [myFactorial_eq_factorial n h]
  have hself : n.toNat ≤ Nat.factorial n.toNat := Nat.self_le_factorial n.toNat
  have hcast : (n.toNat : Int) = n := by unfold Pre at h; omega
  linarith

/-! ## 8. Post-condition (`def Post_prop`) -/

/-- Post-condition combining all behavioral and mathematical properties of `prog` and `myFactorial`. -/
def Post_prop (n : Int) : Prop :=
  invalid_input_prop n ∧
  valid_some_prop n ∧
  base_zero_prop n ∧
  base_one_prop n ∧
  pos_prop n ∧
  mathlib_eq_prop n ∧
  range_prod_prop n ∧
  recurrence_succ_prop n ∧
  recurrence_pred_prop n ∧
  mono_step_prop n ∧
  strict_mono_prop n ∧
  dvd_prop n ∧
  even_prop n ∧
  ge_self_prop n

/-! ## 9. Property-based tests (PBTs) -/

-- Executable Boolean checkers corresponding to each `_prop` and `Post_prop`
def check_invalid_input (n : Int) : Bool :=
  !decide (¬ Pre n) || decide (prog n = none)

def check_valid_some (n : Int) : Bool :=
  decide (prog n = some (myFactorial n)) && (prog n).isSome

def check_base_zero (n : Int) : Bool :=
  !decide (n = 0) || decide (prog n = some 1 ∧ myFactorial n = 1)

def check_base_one (n : Int) : Bool :=
  !decide (n = 1) || decide (prog n = some 1 ∧ myFactorial n = 1)

def check_pos (n : Int) : Bool :=
  decide (myFactorial n ≥ 1) &&
    match prog n with
    | some r => decide (r ≥ 1)
    | none => false

def check_mathlib_eq (n : Int) : Bool :=
  decide (myFactorial n = (Nat.factorial n.toNat : Int)) &&
  decide (prog n = some (Nat.factorial n.toNat : Int))

def check_range_prod (n : Int) : Bool :=
  decide (myFactorial n = ((List.range' 1 n.toNat).prod : Int)) &&
  decide (prog n = some ((List.range' 1 n.toNat).prod : Int))

def check_recurrence_succ (n : Int) : Bool :=
  decide (myFactorial (n + 1) = (n + 1) * myFactorial n) &&
  decide (prog (n + 1) = Option.map (fun r => (n + 1) * r) (prog n))

def check_recurrence_pred (n : Int) : Bool :=
  !decide (n > 0) ||
    (decide (myFactorial n = n * myFactorial (n - 1)) &&
     decide (prog n = Option.map (fun r => n * r) (prog (n - 1))))

def check_mono_step (n : Int) : Bool :=
  decide (myFactorial n ≤ myFactorial (n + 1))

def check_mono_le (m n : Int) : Bool :=
  !decide (Pre m ∧ m ≤ n) || decide (myFactorial m ≤ myFactorial n)

def check_strict_mono (n : Int) : Bool :=
  !decide (n ≥ 1) || decide (myFactorial n < myFactorial (n + 1))

def check_dvd (n : Int) : Bool :=
  !decide (n ≥ 1) || decide (n ∣ myFactorial n)

def check_dvd_of_le (k n : Int) : Bool :=
  !decide (1 ≤ k ∧ k ≤ n) || decide (k ∣ myFactorial n)

def check_even (n : Int) : Bool :=
  !decide (n ≥ 2) || decide (2 ∣ myFactorial n)

def check_ge_self (n : Int) : Bool :=
  decide (myFactorial n ≥ n)

def check_post (n : Int) : Bool :=
  check_invalid_input n &&
  check_valid_some n &&
  check_base_zero n &&
  check_base_one n &&
  check_pos n &&
  check_mathlib_eq n &&
  check_range_prod n &&
  check_recurrence_succ n &&
  check_recurrence_pred n &&
  check_mono_step n &&
  check_strict_mono n &&
  check_dvd n &&
  check_even n &&
  check_ge_self n

-- Randomized PBTs via Plausible
#eval Plausible.Testable.check (∀ n : Int, check_invalid_input n = true)
#eval Plausible.Testable.check (∀ n : Int, Pre n → check_valid_some n = true) { numRetries := 50 }
#eval Plausible.Testable.check (∀ n : Int, check_base_zero n = true)
#eval Plausible.Testable.check (∀ n : Int, check_base_one n = true)
#eval Plausible.Testable.check (∀ n : Int, Pre n → check_pos n = true) { numRetries := 50 }
#eval Plausible.Testable.check (∀ n : Int, Pre n → check_mathlib_eq n = true) { numRetries := 50 }
#eval Plausible.Testable.check (∀ n : Int, Pre n → check_range_prod n = true) { numRetries := 50 }
#eval Plausible.Testable.check (∀ n : Int, Pre n → check_recurrence_succ n = true) { numRetries := 50 }
#eval Plausible.Testable.check (∀ n : Int, Pre n → check_recurrence_pred n = true) { numRetries := 50 }
#eval Plausible.Testable.check (∀ n : Int, Pre n → check_mono_step n = true) { numRetries := 50 }
#eval Plausible.Testable.check (∀ m n : Int, check_mono_le m n = true)
#eval Plausible.Testable.check (∀ n : Int, Pre n → check_strict_mono n = true) { numRetries := 50 }
#eval Plausible.Testable.check (∀ n : Int, Pre n → check_dvd n = true) { numRetries := 50 }
#eval Plausible.Testable.check (∀ k n : Int, check_dvd_of_le k n = true)
#eval Plausible.Testable.check (∀ n : Int, Pre n → check_even n = true) { numRetries := 50 }
#eval Plausible.Testable.check (∀ n : Int, Pre n → check_ge_self n = true) { numRetries := 50 }
#eval Plausible.Testable.check (∀ n : Int, Pre n → check_post n = true) { numRetries := 50 }

-- Bounded exhaustive PBTs over small inputs (including negative inputs for `check_invalid_input`)
example : (List.range 30).all (fun k => check_invalid_input (-((k : Int) + 1))) = true := by native_decide
example : (List.range 25).all (fun k => check_valid_some (k : Int)) = true := by native_decide
example : (List.range 25).all (fun k => check_base_zero (k : Int)) = true := by native_decide
example : (List.range 25).all (fun k => check_base_one (k : Int)) = true := by native_decide
example : (List.range 25).all (fun k => check_pos (k : Int)) = true := by native_decide
example : (List.range 25).all (fun k => check_mathlib_eq (k : Int)) = true := by native_decide
example : (List.range 25).all (fun k => check_range_prod (k : Int)) = true := by native_decide
example : (List.range 25).all (fun k => check_recurrence_succ (k : Int)) = true := by native_decide
example : (List.range 25).all (fun k => check_recurrence_pred (k : Int)) = true := by native_decide
example : (List.range 25).all (fun k => check_mono_step (k : Int)) = true := by native_decide
example : (List.range 15).all (fun m => (List.range 15).all (fun n => check_mono_le (m : Int) (n : Int))) = true := by native_decide
example : (List.range 25).all (fun k => check_strict_mono (k : Int)) = true := by native_decide
example : (List.range 25).all (fun k => check_dvd (k : Int)) = true := by native_decide
example : (List.range 15).all (fun k => (List.range 15).all (fun n => check_dvd_of_le (k : Int) (n : Int))) = true := by native_decide
example : (List.range 25).all (fun k => check_even (k : Int)) = true := by native_decide
example : (List.range 25).all (fun k => check_ge_self (k : Int)) = true := by native_decide
example : (List.range 25).all (fun k => check_post (k : Int)) = true := by native_decide

/-! ## 10. Correctness theorem (`Pre -> Post`) -/

/-- Main correctness theorem: for any integer `n` satisfying `Pre n`, `Post_prop n` holds. -/
theorem correctness_thm (n : Int) (h : Pre n) : Post_prop n :=
  ⟨invalid_input_thm n,
   valid_some_thm n h,
   base_zero_thm n,
   base_one_thm n,
   pos_thm n h,
   mathlib_eq_thm n h,
   range_prod_thm n h,
   recurrence_succ_thm n h,
   recurrence_pred_thm n h,
   mono_step_thm n h,
   strict_mono_thm n h,
   dvd_thm n h,
   even_thm n h,
   ge_self_thm n h⟩

/-! ## 11. Imperative implementation using `Id.run do` with mutable state -/

/-- Imperative implementation of `factorialNat` on natural numbers. -/
def factorialNatImp (n : Nat) : Nat := Id.run do
  if n == 0 then
    return 1
  let mut result : Nat := 1
  for i in [1 : n + 1] do
    result := result * i
  return result

/-- Imperative implementation of `myFactorial` using `Id.run do` and mutable `result`. -/
def myFactorialImp (n : Int) : Int := Id.run do
  if n ≤ 0 then
    return 1
  let mut result : Int := 1
  for i in [1 : n.toNat + 1] do
    result := result * (i : Int)
  return result

/-- Imperative implementation of `prog(n: int)` matching the Python loop structure line by line. -/
def progImp (n : Int) : Option Int := Id.run do
  if ¬ pre n then
    return none
  if n == 0 then
    return some 1
  let mut result : Int := 1
  for i in [1 : n.toNat + 1] do
    result := result * (i : Int)
  return some result

/-! ## 12. Imperative tests -/

example : progImp 3 = some 6 := by native_decide
example : progImp 0 = some 1 := by native_decide
example : progImp 1 = some 1 := by native_decide
example : progImp 2 = some 2 := by native_decide
example : progImp 4 = some 24 := by native_decide
example : progImp 5 = some 120 := by native_decide
example : progImp (-1) = none := by native_decide
example : progImp (-5) = none := by native_decide

example : myFactorialImp 0 = 1 := by native_decide
example : myFactorialImp 1 = 1 := by native_decide
example : myFactorialImp 3 = 6 := by native_decide
example : myFactorialImp 5 = 120 := by native_decide

example : factorialNatImp 0 = 1 := by native_decide
example : factorialNatImp 1 = 1 := by native_decide
example : factorialNatImp 3 = 6 := by native_decide
example : factorialNatImp 5 = 120 := by native_decide

#eval progImp 3
#eval progImp 0
#eval progImp 1
#eval progImp (-1)
#eval myFactorialImp 3
#eval factorialNatImp 3

/-! ## 13. Equivalence theorem: functional = imperative -/

theorem factorialNat_eq_factorialNatImp (n : Nat) :
    factorialNat n = factorialNatImp n := by
  rw [factorialNat_eq_factorial]
  unfold factorialNatImp
  by_cases hn0 : (n == 0) = true
  · have h : n = 0 := beq_iff_eq.mp hn0
    subst h
    simp
  · simp [hn0, Std.Range.forIn_eq_forIn_range', foldl_nat_range'_eq_factorial]

theorem myFactorial_eq_myFactorialImp (n : Int) :
    myFactorial n = myFactorialImp n := by
  unfold myFactorial myFactorialImp
  split_ifs with hle
  · simp
  · simp [Std.Range.forIn_eq_forIn_range']

theorem prog_eq_progImp (n : Int) :
    prog n = progImp n := by
  unfold prog progImp
  by_cases hpre : pre n = true
  · by_cases hn0 : (n == 0) = true
    · simp [hpre, hn0]
    · simp [hpre, hn0, Std.Range.forIn_eq_forIn_range']
  · simp [hpre]

theorem equivalence_thm : prog = progImp := by
  funext n
  exact prog_eq_progImp n

end «16_MyFactorial»
